module

public import Proof.CalderonN.NormalSecondVariation
public import Proof.CalderonN.LocalThirdFlowVariation
public import Proof.CalderonN.NormalEndpointJets

import Mathlib.Tactic

/-! Adapted from the third variational equation in the checked Proposition 5.3 release. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem NormalCoordinates.hasDerivAt_third_phase_variation {Y Ω : Set (X dim)}
    (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) 
    {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (h k l : (X dim))
    (hv : v ∈ interior (disk g y (R y))) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => thirdParameterVariation (normalGeodesicPhase expMap y) h k l (v,s))
      (fderiv ℝ (coordinateGeodesicSpray g) (normalGeodesicPhase expMap y (v,t))
          (thirdParameterVariation (normalGeodesicPhase expMap y) h k l (v,t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalGeodesicPhase expMap y (v,t))
          (firstParameterVariation (normalGeodesicPhase expMap y) l (v,t))
          (secondParameterVariation (normalGeodesicPhase expMap y) h k (v,t))+
        fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g))) (normalGeodesicPhase expMap y (v,t))
          (firstParameterVariation (normalGeodesicPhase expMap y) l (v,t))
          (firstParameterVariation (normalGeodesicPhase expMap y) k (v,t))
          (firstParameterVariation (normalGeodesicPhase expMap y) h (v,t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalGeodesicPhase expMap y (v,t))
          (secondParameterVariation (normalGeodesicPhase expMap y) k l (v,t))
          (firstParameterVariation (normalGeodesicPhase expMap y) h (v,t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalGeodesicPhase expMap y (v,t))
          (firstParameterVariation (normalGeodesicPhase expMap y) k (v,t))
          (secondParameterVariation (normalGeodesicPhase expMap y) h l (v,t))) t := by
  have hvd := interior_subset hv
  have hPhase := hN.contDiffAt_phase hy (v,t) (smul_mem_disk_of_mem g y v (R y) t hvd ht)
  have hPos : (normalGeodesicPhase expMap y (v,t)).1 ∈ Ω := hN.path_image hy v hvd ht
  have hSpray := hg.contDiffAt_coordinateGeodesicSpray hΩ hK _ hPos
  let P := normalGeodesicPhase expMap y
  have hSTime : (fun x => fderiv ℝ (secondParameterVariation P h k) (x,t) (0,1)) =ᶠ[𝓝 v]
      (fun x => fderiv ℝ (coordinateGeodesicSpray g) (P (x,t))
        (secondParameterVariation P h k (x,t)) +
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P (x,t))
          (firstParameterVariation P k (x,t)) (firstParameterVariation P h (x,t))) := by
    filter_upwards [isOpen_interior.mem_nhds hv] with x hx
    have hPx := hN.contDiffAt_phase hy (x,t)
      (smul_mem_disk_of_mem g y x (R y) t (interior_subset hx) ht)
    have hS := contDiffAt_secondParameterVariation P h k (x,t) hPx
    exact (hasDerivAt_time_slice (secondParameterVariation P h k) x t
      (hS.differentiableAt (by simp))).unique
      (hN.hasDerivAt_second_phase_variation hΩ hg hK hy x h k hx ht)
  exact hasDerivAt_third_parameter_variation P (coordinateGeodesicSpray g)
    v h k l t hPhase hSpray hSTime

lemma NormalCoordinates.third_phase_variation_zero {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v h k l : (X dim)) (hv : v ∈ interior (disk g y (R y))) :
    thirdParameterVariation (normalGeodesicPhase expMap y) h k l (v,0) = 0 := by
  let P := normalGeodesicPhase expMap y
  have hPhase := hN.contDiffAt_phase hy (v,0)
    (by simpa only [zero_smul] using zero_mem_disk g y (R y))
  have hS := contDiffAt_secondParameterVariation P h k (v,0) hPhase
  have hEq : (fun x : (X dim) => secondParameterVariation P h k (x,0)) =ᶠ[𝓝 v] (fun _ => 0) := by
    filter_upwards [isOpen_interior.mem_nhds hv] with x hx
    exact hN.second_phase_variation_zero hy x h k hx
  rw [thirdParameterVariation,← fderiv_base_slice_of_contDiffAt _ v l 0 hS,hEq.fderiv_eq]
  simp

end CalderonN
