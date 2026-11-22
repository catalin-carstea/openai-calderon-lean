module

import Proof.CalderonN.NormalEndpointJets
import Proof.CalderonN.CoordinateSprayBounds
public import Proof.CalderonN.LocalSecondFlowVariation
public import Proof.CalderonN.NormalGeodesicVariation

import Mathlib.Tactic

/-! Adapted from `NormalSecondVariation` in the checked Proposition 5.3 release. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The actual normal map satisfies the second initial-velocity variational equation. -/
theorem NormalCoordinates.hasDerivAt_second_phase_variation {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u k : (X dim)) (hv : v ∈ interior (disk g y (R y))) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s : ℝ => secondParameterVariation (normalGeodesicPhase expMap y) u k (v,s))
      (fderiv ℝ (coordinateGeodesicSpray g) (normalGeodesicPhase expMap y (v,t))
          (secondParameterVariation (normalGeodesicPhase expMap y) u k (v,t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalGeodesicPhase expMap y (v,t))
          (firstParameterVariation (normalGeodesicPhase expMap y) k (v,t))
          (firstParameterVariation (normalGeodesicPhase expMap y) u (v,t))) t := by
  have hvd : v ∈ disk g y (R y) := interior_subset hv
  have hPhase := hN.contDiffAt_phase hy (v,t) (smul_mem_disk_of_mem g y v (R y) t hvd ht)
  have hPos : (normalGeodesicPhase expMap y (v,t)).1 ∈ Ω := hN.path_image hy v hvd ht
  have hSpray := hg.contDiffAt_coordinateGeodesicSpray hΩ hK _ hPos
  have hJTime : (fun x => fderiv ℝ (firstParameterVariation (normalGeodesicPhase expMap y) u) (x,t) (0,1)) =ᶠ[𝓝 v]
      (fun x => fderiv ℝ (coordinateGeodesicSpray g) (normalGeodesicPhase expMap y (x,t))
        (firstParameterVariation (normalGeodesicPhase expMap y) u (x,t))) := by
    filter_upwards [isOpen_interior.mem_nhds hv] with x hx
    have hPx := hN.contDiffAt_phase hy (x,t)
      (smul_mem_disk_of_mem g y x (R y) t (interior_subset hx) ht)
    have hJ := contDiffAt_firstParameterVariation (normalGeodesicPhase expMap y) u (x,t) hPx
    have hTime := hasDerivAt_time_slice (firstParameterVariation (normalGeodesicPhase expMap y) u)
      x t (hJ.differentiableAt (by simp))
    exact hTime.unique (hN.hasDerivAt_phase_variation hΩ hg hK hy x u hx ht)
  exact hasDerivAt_second_parameter_variation (normalGeodesicPhase expMap y)
    (coordinateGeodesicSpray g) v u k t hPhase hSpray hJTime

lemma NormalCoordinates.second_phase_variation_zero {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u k : (X dim)) (hv : v ∈ interior (disk g y (R y))) :
    secondParameterVariation (normalGeodesicPhase expMap y) u k (v,0) = 0 := by
  have hPhase := hN.contDiffAt_phase hy (v,0)
    (by simpa only [zero_smul] using zero_mem_disk g y (R y))
  have hJ := contDiffAt_firstParameterVariation (normalGeodesicPhase expMap y) u (v,0) hPhase
  have heq : (fun x => firstParameterVariation (normalGeodesicPhase expMap y) u (x,0)) =ᶠ[𝓝 v]
      (fun _ : (X dim) => ((0:(X dim)),u)) := by
    filter_upwards [isOpen_interior.mem_nhds hv] with x hx
    exact hN.phase_variation_zero hy x u hx
  rw [secondParameterVariation,← fderiv_base_slice_of_contDiffAt _ v k 0 hJ,heq.fderiv_eq]
  simp

end CalderonN
