import Proof.FirstDensityThirdJet
import Proof.FirstDensityEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def firstDensityJetEnvelope (K M1 M2 M3 : ℝ) : ℝ :=
  K+K^2*M1+(K^2*M2+2*K^3*M1^2)+thirdFirstDensityBudget K M1 M2 M3

/-- The actual density scalar and its reciprocal share one envelope through
    three derivatives, uniformly from the same metric jets. -/
theorem Background.firstMetricDensityFactors_jet_envelope {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m) {x : X} (hx : x ∈ Ω) :
    (∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n (firstMetricDensityFactor g g₁) x‖ ≤
      firstDensityJetEnvelope K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩|) ∧
    (∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n (fun y => (firstMetricDensityFactor g g₁ y)⁻¹) x‖ ≤
      firstDensityJetEnvelope K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩|) := by
  let t := firstMetricConformalDepth g g₁
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let M3 := |M ⟨3,by omega⟩|
  let T1 := K*M1
  let T2 := K*M2+K^2*M1^2
  let T3 := thirdConformalDepthBudget K M1 M2 M3
  let P1 := K^2*M1
  let P2 := K^2*M2+2*K^3*M1^2
  let P3 := thirdFirstDensityBudget K M1 M2 M3
  have hT1 : 0 ≤ T1 := by dsimp [T1,M1];positivity
  have hT2 : 0 ≤ T2 := by dsimp [T2,M1,M2];positivity
  have hT3 : 0 ≤ T3 := by dsimp [T3,thirdConformalDepthBudget,M1,M2,M3];positivity
  have hP1 : 0 ≤ P1 := by dsimp [P1,M1];positivity
  have hP2 : 0 ≤ P2 := by dsimp [P2,M1,M2];positivity
  have hP3 : 0 ≤ P3 := by dsimp [P3,thirdFirstDensityBudget,thirdConformalDepthBudget,M1,M2,M3];positivity
  have ht := h.firstMetricConformalDepth_smooth hK
  have htAt := ht.contDiffAt (hΩ.mem_nhds hx)
  have hLow := h.firstMetricConformalDepth_jet_bounds hΩ hK (by omega) hx
  have hHigh := h.firstMetricConformalDepth_third_jet_bound hΩ hK hm hx
  have hSigned (s : ℝ) (hs : |s| = 1) (hValue : Real.exp (s*t x) ≤ K) :
      ∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n (fun y => Real.exp (s*t y)) x‖ ≤ K+P1+P2+P3 := by
    let F := fun y => s*t y
    have hF : ContDiffOn ℝ ∞ F Ω := ht.const_smul s
    have hNorm (n : ℕ) : ‖iteratedFDeriv ℝ n F x‖ = ‖iteratedFDeriv ℝ n t x‖ := by
      change ‖iteratedFDeriv ℝ n (s • t) x‖ = _
      rw [iteratedFDeriv_const_smul_apply (htAt.of_le (by simp)),norm_smul,Real.norm_eq_abs,hs,one_mul]
    have hD : ‖fderiv ℝ F x‖ ≤ T1 := by rw [← norm_iteratedFDeriv_one,hNorm,norm_iteratedFDeriv_one];exact hLow.1
    have hDD : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ T2 := by rw [← norm_iteratedFDeriv_two_eq_nested,hNorm,norm_iteratedFDeriv_two_eq_nested];exact hLow.2
    have hDDD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x‖ ≤ T3 := by rw [← norm_iteratedFDeriv_three_eq_nested,hNorm,norm_iteratedFDeriv_three_eq_nested];exact hHigh
    have hb1 : ‖fderiv ℝ (fun y => Real.exp (F y)) x‖ ≤ P1 :=
      (norm_fderiv_exp_comp_le F x ((hF.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) T1 hD).trans
        ((mul_le_mul_of_nonneg_right hValue hT1).trans_eq (by dsimp only [T1,P1];ring))
    have hb2 : ‖fderiv ℝ (fderiv ℝ (fun y => Real.exp (F y))) x‖ ≤ P2 :=
      (norm_second_fderiv_exp_comp_le F x (hF.contDiffAt (hΩ.mem_nhds hx)) T1 T2 hT1 hT2 hD hDD).trans
        ((mul_le_mul_of_nonneg_right hValue (by positivity)).trans_eq (by dsimp only [T1,T2,P2];ring))
    have hb3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => Real.exp (F y)))) x‖ ≤ P3 :=
      (norm_third_fderiv_exp_comp_le hΩ F hF hx T1 T2 T3 hT1 hT2 hT3 hD hDD hDDD).trans
        ((mul_le_mul_of_nonneg_right hValue (by positivity)).trans_eq (by rfl))
    intro n hn
    interval_cases n
    · simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      linarith only [hValue,hP1,hP2,hP3]
    · rw [norm_iteratedFDeriv_one];exact hb1.trans (by linarith only [hK,hP2,hP3])
    · rw [norm_iteratedFDeriv_two_eq_nested];exact hb2.trans (by linarith only [hK,hP1,hP3])
    · rw [norm_iteratedFDeriv_three_eq_nested];exact hb3.trans (by linarith only [hK,hP1,hP2])
  have hMinus := hSigned (-1) (by norm_num) (by simpa only [neg_one_mul,t,firstMetricDensityFactor] using h.firstMetricDensityFactor_le hK hx)
  have hInvFun : (fun y => (firstMetricDensityFactor g g₁ y)⁻¹) = fun y => Real.exp (t y) := by
    funext y
    simp only [firstMetricDensityFactor,Real.exp_neg,inv_inv,t]
  have hPlus := hSigned 1 (by norm_num) (by
    simpa only [one_mul] using (congrFun hInvFun x ▸ h.firstMetricDensityFactor_inverse_le hK hx))
  constructor
  · intro n hn
    change ‖iteratedFDeriv ℝ n (fun y => Real.exp (-t y)) x‖ ≤ _
    simpa only [neg_one_mul,firstDensityJetEnvelope,P1,P2,P3,M1,M2,M3] using hMinus n hn
  · rw [hInvFun]
    simpa only [one_mul,firstDensityJetEnvelope,P1,P2,P3,M1,M2,M3] using hPlus

end ShrinkingSpheres
