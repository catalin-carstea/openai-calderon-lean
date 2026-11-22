module

public import Proof.CalderonN.NormalGeodesicPhase

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The first initial-velocity variation of the actual admitted normal map satisfies
    the linearized coordinate spray equation. The initial velocity is only required
    to lie in the interior of the same admitted normal disk. -/
theorem NormalCoordinates.hasDerivAt_phase_variation {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (hv : v ∈ interior (disk g y (R y))) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (normalGeodesicPhase expMap y) (v,s) (u,0))
      (fderiv ℝ (coordinateGeodesicSpray g) (normalGeodesicPhase expMap y (v,t))
        (fderiv ℝ (normalGeodesicPhase expMap y) (v,t) (u,0))) t := by
  have hvd : v ∈ disk g y (R y) := interior_subset hv
  have hPhase := hN.contDiffAt_phase hy (v,t) (smul_mem_disk_of_mem g y v (R y) t hvd ht)
  have hPos : (normalGeodesicPhase expMap y (v,t)).1 ∈ Ω := hN.path_image hy v hvd ht
  have hSpray := (hg.contDiffAt_coordinateGeodesicSpray hΩ hK _ hPos).differentiableAt (by simp)
  have hODE : (fun x => fderiv ℝ (normalGeodesicPhase expMap y) (x,t) (0,1)) =ᶠ[𝓝 v]
      (fun x => coordinateGeodesicSpray g (normalGeodesicPhase expMap y (x,t))) := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hv] with x hx
    have hPx := hN.contDiffAt_phase hy (x,t) (smul_mem_disk_of_mem g y x (R y) t hx ht)
    have hTime := hasDerivAt_time_slice (normalGeodesicPhase expMap y) x t (hPx.differentiableAt (by simp))
    exact hTime.unique (hN.hasDerivAt_phase hy x hx ht)
  exact hasDerivAt_parameter_variation (normalGeodesicPhase expMap y) (coordinateGeodesicSpray g)
    v u t hPhase hSpray hODE

/-- The first velocity variation starts at (0,u), for the actual map. -/
theorem NormalCoordinates.phase_variation_zero {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (hv : v ∈ interior (disk g y (R y))) :
    fderiv ℝ (normalGeodesicPhase expMap y) (v,0) (u,0) = (0,u) := by
  have hPhase := hN.contDiffAt_phase hy (v,0) (by simpa only [zero_smul] using zero_mem_disk g y (R y))
  have heq : (fun x => normalGeodesicPhase expMap y (x,0)) =ᶠ[𝓝 v] (fun x : (X dim) => (y,x)) := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hv] with x hx
    exact hN.phase_zero hy x hx
  rw [← fderiv_base_slice_of_contDiffAt (normalGeodesicPhase expMap y) v u 0 hPhase,heq.fderiv_eq]
  have hd : HasFDerivAt (fun x : (X dim) => (y,x)) ((0:(X dim) →L[ℝ] (X dim)).prod (ContinuousLinearMap.id ℝ (X dim))) v :=
    (hasFDerivAt_const (𝕜:=ℝ) y v).prodMk (hasFDerivAt_id v)
  rw [hd.fderiv]
  rfl

end CalderonN
