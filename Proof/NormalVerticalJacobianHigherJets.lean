import Proof.FiniteJetBoundCalculus
import Proof.UniformNormalMapHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalVerticalRestrictionL : ((X × X) →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) :=
  (ContinuousLinearMap.compL ℝ X (X × X) X).flip (ContinuousLinearMap.inr ℝ X X)

lemma norm_normalVerticalRestrictionL_le_one : ‖normalVerticalRestrictionL‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro D
  change ‖D.comp (ContinuousLinearMap.inr ℝ X X)‖ ≤ 1*‖D‖
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [mul_one,one_mul] using mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inr_le_one (𝕜:=ℝ) (E:=X) (F:=X)) (norm_nonneg D))

theorem norm_iteratedFDeriv_normalVerticalJacobian_le (E : X × X → X) (p : X × X)
    (hE : ContDiffAt ℝ ∞ E p) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q : X × X => normalVerticalJacobian E q.1 q.2) p‖ ≤
      ‖iteratedFDeriv ℝ (n+1) E p‖ := by
  have hh := norm_iteratedFDeriv_clm_comp_le normalVerticalRestrictionL (fderiv ℝ E) p
    (hE.fderiv_right (m:=∞) (by simp)) n
  change ‖iteratedFDeriv ℝ n (fun q : X × X => normalVerticalJacobian E q.1 q.2) p‖ ≤
    ‖normalVerticalRestrictionL‖*‖iteratedFDeriv ℝ n (fderiv ℝ E) p‖ at hh
  rw [norm_iteratedFDeriv_fderiv] at hh
  exact hh.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      norm_normalVerticalRestrictionL_le_one (norm_nonneg (iteratedFDeriv ℝ (n+1) E p)))

theorem uniform_normalVerticalJacobian_higher_jet_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    (K : ℝ) (hK : 0 < K) {m : ℕ} (M : Fin (m+1) → ℝ)
    (N : ℕ) (hNm : N+2 ≤ m) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),
      Background Ω K M g g₁ g₂ e → ∀ (Y : Set X), IsOpen Y →
      ∀ (E : X × X → X) (R : X → ℝ), NormalCoordinates Y Ω g E R →
      ∀ y ∈ Y, ContinuousAt R y → ∀ v : X,
      metricPair g y v v < (R y)^2 → ‖v‖ ≤ 1 →
      ∀ n : ℕ,n ≤ N →
        ‖iteratedFDeriv ℝ n (fun p : X × X => normalVerticalJacobian E p.1 p.2) (y,v)‖ ≤ C := by
  obtain ⟨C,hC,hBound⟩ := uniform_normalMap_higher_jet_bounds hΩ K hK M (N+1) (by omega)
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e h Y hY E R hN y hy hR v hv hv1 n hn
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ E (y,v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv.le⟩))
  exact (norm_iteratedFDeriv_normalVerticalJacobian_le E (y,v) hE n).trans
    (hBound g g₁ g₂ e h Y hY E R hN y hy hR v hv hv1 (n+1) (by omega) (by omega)).2

end ShrinkingSpheres
