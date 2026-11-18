import Proof.LocalMixedParameterJetCalculus
import Proof.ParameterSpatialJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiffAt_radialFirst_left_slice_of_open
    (F : P × ℝ → V) {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (t : ℝ) (hp : (p,t) ∈ U) :
    ContDiffAt ℝ ∞ (fun q => radialFirstDerivative F (q,t)) p := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hp
  have hRad : (fun q => radialFirstDerivative G (q,t)) =ᶠ[𝓝 p]
      (fun q => radialFirstDerivative F (q,t)) :=
    (radialFirstDerivative_congr_nhds he).comp_tendsto
      (continuousAt_id.prodMk continuousAt_const).tendsto
  exact (((contDiff_radialFirstDerivative G hG).comp
    (contDiff_id.prodMk contDiff_const)).contDiffAt).congr_of_eventuallyEq hRad.symm

/-- A radial derivative is a unit-direction contraction of the next joint
    derivative. A local smooth extension is used only to identify germs. -/
theorem norm_iteratedFDeriv_radialFirstDerivative_of_open_le
    (F : P × ℝ → V) {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (t : ℝ) (hp : (p,t) ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (radialFirstDerivative F) (p,t)‖ ≤ ‖iteratedFDeriv ℝ (n+1) F (p,t)‖ := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hp
  have hRad := radialFirstDerivative_congr_nhds he
  rw [← (hRad.iteratedFDeriv ℝ n).eq_of_nhds,← (he.iteratedFDeriv ℝ (n+1)).eq_of_nhds]
  let ev : ((P × ℝ) →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V ((0:P),(1:ℝ))
  have hv : ‖((0:P),(1:ℝ))‖ = 1 := by simp only [Prod.norm_def,norm_zero,norm_one,max_eq_right zero_le_one]
  have hEv : ‖ev‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    exact (A.le_opNorm ((0:P),(1:ℝ))).trans_eq (by rw [hv];ring)
  have hDG : ContDiffAt ℝ ∞ (fderiv ℝ G) (p,t) :=
    (hG.fderiv_right (m:=∞) (by simp)).contDiffAt
  have hBound := norm_iteratedFDeriv_clm_comp_le ev (fderiv ℝ G) (p,t) hDG n
  change ‖iteratedFDeriv ℝ n (ev ∘ fderiv ℝ G) (p,t)‖ ≤ _
  exact hBound.trans ((mul_le_mul_of_nonneg_right hEv (norm_nonneg _)).trans_eq (by
    rw [one_mul,norm_iteratedFDeriv_fderiv]))

theorem norm_iteratedFDeriv_radialFirst_left_slice_of_open_le
    (F : P × ℝ → V) {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (t : ℝ) (hp : (p,t) ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => radialFirstDerivative F (q,t)) p‖ ≤
      ‖iteratedFDeriv ℝ (n+1) F (p,t)‖ := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hp
  have hRad := (radialFirstDerivative_congr_nhds he).comp_tendsto
    (continuousAt_id.prodMk continuousAt_const).tendsto
  change (fun q => radialFirstDerivative G (q,t)) =ᶠ[𝓝 p]
    (fun q => radialFirstDerivative F (q,t)) at hRad
  rw [← (hRad.iteratedFDeriv ℝ n).eq_of_nhds,← (he.iteratedFDeriv ℝ (n+1)).eq_of_nhds]
  exact (norm_iteratedFDeriv_left_slice_le (radialFirstDerivative G) (contDiff_radialFirstDerivative G hG)
    p t n).trans (norm_iteratedFDeriv_radialFirstDerivative_of_open_le G isOpen_univ hG.contDiffOn p t (mem_univ _) n)

end ShrinkingSpheres
