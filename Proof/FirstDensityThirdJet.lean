import Proof.ThirdScalarFunctionJets
import Proof.FirstMetricDensityFactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def thirdConformalDepthBudget (K M1 M2 M3 : ℝ) : ℝ :=
  K*M3+3*K^2*M1*M2+2*K^3*M1^3

theorem Background.firstMetricConformalDepth_third_jet_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m) {x : X} (hx : x ∈ Ω) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (firstMetricConformalDepth g g₁))) x‖ ≤
      thirdConformalDepthBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩| := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let M3 := |M ⟨3,by omega⟩|
  let T := thirdConformalDepthBudget K M1 M2 M3
  have hLog (g' : MetricField) (hmem : g' ∈ ({g,g₁}:Set MetricField)) :
      ‖iteratedFDeriv ℝ 3 (fun y => Real.log (g' y 0 0)) x‖ ≤ T := by
    have hg' : Elliptic Ω K g' := by
      simp only [mem_insert_iff,mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl
      · exact h.1
      · exact h.2.1
    have hPos := hg'.diagonal_entry_pos hK hx 0
    have hInv0 : 0 ≤ (g' x 0 0)⁻¹ := (inv_pos.mpr hPos).le
    have hInv := hg'.diagonal_inverse_le hK hx 0
    have hD : ‖fderiv ℝ (fun y => g' y 0 0) x‖ ≤ M1 := by
      have hb := h.2.2.2.2.1 g' hmem ⟨1,by omega⟩ 0 0 x hx
      rw [norm_iteratedFDeriv_one] at hb
      exact hb.trans (le_abs_self _)
    have hDD : ‖fderiv ℝ (fderiv ℝ (fun y => g' y 0 0)) x‖ ≤ M2 := by
      have hb := h.2.2.2.2.1 g' hmem ⟨2,by omega⟩ 0 0 x hx
      rw [norm_iteratedFDeriv_two_eq_nested] at hb
      exact hb.trans (le_abs_self _)
    have hDDD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => g' y 0 0))) x‖ ≤ M3 := by
      have hb := h.2.2.2.2.1 g' hmem ⟨3,by omega⟩ 0 0 x hx
      rw [norm_iteratedFDeriv_three_eq_nested] at hb
      exact hb.trans (le_abs_self _)
    rw [norm_iteratedFDeriv_three_eq_nested]
    have hb := norm_third_fderiv_log_le hΩ (fun y => g' y 0 0) (hg'.1 0 0)
      (fun y hy => hg'.diagonal_entry_pos hK hy 0) hx M1 M2 M3
      (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hD hDD hDDD
    exact hb.trans (by dsimp only [T,thirdConformalDepthBudget];gcongr)
  let f := fun y => Real.log (g y 0 0)
  let j := fun y => Real.log (g₁ y 0 0)
  have hf : ContDiffAt ℝ ∞ f x := ((h.1.1 0 0).log (fun y hy => (h.1.diagonal_entry_pos hK hy 0).ne')).contDiffAt (hΩ.mem_nhds hx)
  have hj : ContDiffAt ℝ ∞ j x := ((h.2.1.1 0 0).log (fun y hy => (h.2.1.diagonal_entry_pos hK hy 0).ne')).contDiffAt (hΩ.mem_nhds hx)
  have hγ := hLog g (by simp)
  have h1 := hLog g₁ (by simp)
  rw [← norm_iteratedFDeriv_three_eq_nested]
  change ‖iteratedFDeriv ℝ 3 (fun y => (1/2:ℝ) • (f y-j y)) x‖ ≤ T
  rw [iteratedFDeriv_const_smul_apply' ((hf.sub hj).of_le (by simp))]
  change ‖(1/2:ℝ) • iteratedFDeriv ℝ 3 (f-j) x‖ ≤ T
  rw [iteratedFDeriv_sub_apply (hf.of_le (by simp)) (hj.of_le (by simp)),norm_smul,Real.norm_eq_abs]
  have hb := (norm_sub_le (iteratedFDeriv ℝ 3 f x) (iteratedFDeriv ℝ 3 j x)).trans (add_le_add hγ h1)
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg (1/2:ℝ))).trans_eq (by norm_num;ring)

def thirdFirstDensityBudget (K M1 M2 M3 : ℝ) : ℝ :=
  let T1 := K*M1
  let T2 := K*M2+K^2*M1^2
  K*(thirdConformalDepthBudget K M1 M2 M3+3*T1*T2+T1^3)

/-- The actual dimension-three divergence density has a uniform third jet
    from the frozen metric budgets, with no compact-family extra premise. -/
theorem Background.firstMetricDensityFactor_third_jet_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m) {x : X} (hx : x ∈ Ω) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (firstMetricDensityFactor g g₁))) x‖ ≤
      thirdFirstDensityBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩| := by
  let t := firstMetricConformalDepth g g₁
  let F := fun y => -t y
  let T1 := K*|M ⟨1,by omega⟩|
  let T2 := K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2
  let T3 := thirdConformalDepthBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩|
  have hT1 : 0 ≤ T1 := by dsimp [T1];positivity
  have hT2 : 0 ≤ T2 := by dsimp [T2];positivity
  have hT3 : 0 ≤ T3 := by dsimp [T3,thirdConformalDepthBudget];positivity
  have hSmooth : ContDiffOn ℝ ∞ F Ω := (h.firstMetricConformalDepth_smooth hK).neg
  have hLow := h.firstMetricConformalDepth_jet_bounds hΩ hK (by omega) hx
  have hHigh := h.firstMetricConformalDepth_third_jet_bound hΩ hK hm hx
  have hD : ‖fderiv ℝ F x‖ ≤ T1 := by simpa only [F,fderiv_fun_neg,norm_neg] using hLow.1
  have hDD : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ T2 := by
    rw [← norm_iteratedFDeriv_two_eq_nested]
    change ‖iteratedFDeriv ℝ 2 (-t) x‖ ≤ T2
    rw [iteratedFDeriv_neg_apply,norm_neg,norm_iteratedFDeriv_two_eq_nested]
    exact hLow.2
  have hDDD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x‖ ≤ T3 := by
    rw [← norm_iteratedFDeriv_three_eq_nested]
    change ‖iteratedFDeriv ℝ 3 (-t) x‖ ≤ T3
    rw [iteratedFDeriv_neg_apply,norm_neg,norm_iteratedFDeriv_three_eq_nested]
    exact hHigh
  have hb := norm_third_fderiv_exp_comp_le hΩ F hSmooth hx T1 T2 T3 hT1 hT2 hT3 hD hDD hDDD
  have hValue : Real.exp (F x) ≤ K := h.firstMetricDensityFactor_le hK hx
  exact hb.trans ((mul_le_mul_of_nonneg_right hValue (by positivity)).trans_eq (by rfl))

end ShrinkingSpheres
