import Proof.CoarseCovariantSecondProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ShrinkingSpheres.ParallelEnergy

/-- The four true weighted second-jet coefficients have the same estimate
at every normed endpoint. -/
lemma norm_second_weighted_jet_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F Sb Sc T : E) (w wb wc wbc B C0 C1 C2 r β : ℝ)
    (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hw : |w| ≤ B) (hwb : |wb| ≤ B*β) (hwc : |wc| ≤ B*β) (hwbc : |wbc| ≤ B*β^2)
    (hF : ‖F‖ ≤ C0*r) (hSb : ‖Sb‖ ≤ C1*r*β) (hSc : ‖Sc‖ ≤ C1*r*β)
    (hT : ‖T‖ ≤ C2*r*β^2) :
    ‖(w • T+wc • Sb)+(wb • Sc+wbc • F)‖ ≤ B*(C2+2*C1+C0)*r*β^2 := by
  have h0 : ‖w • T‖ ≤ B*(C2*r*β^2) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hw hT (norm_nonneg _) hB
  have h1 : ‖wc • Sb‖ ≤ (B*β)*(C1*r*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwc hSb (norm_nonneg _) (mul_nonneg hB hβ)
  have h2 : ‖wb • Sc‖ ≤ (B*β)*(C1*r*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwb hSc (norm_nonneg _) (mul_nonneg hB hβ)
  have h3 : ‖wbc • F‖ ≤ (B*β^2)*(C0*r) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwbc hF (norm_nonneg _) (mul_nonneg hB (sq_nonneg _))
  calc
    _ ≤ (‖w • T‖+‖wc • Sb‖)+(‖wb • Sc‖+‖wbc • F‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ (B*(C2*r*β^2)+(B*β)*(C1*r*β))+((B*β)*(C1*r*β)+(B*β^2)*(C0*r)) :=
      add_le_add (add_le_add h0 h1) (add_le_add h2 h3)
    _ = _ := by ring

/-- The natural epsilon/beta, epsilon, epsilon beta weights survive at
any genuine normed endpoint. -/
lemma small_two_jet_product_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F Sb Sc T : E)
    (w wb wc wbc B Q ε β : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hw : |w| ≤ B*ε/β) (hwb : |wb| ≤ B*ε) (hwc : |wc| ≤ B*ε) (hwbc : |wbc| ≤ B*ε*β)
    (hF : ‖F‖ ≤ Q) (hSb : ‖Sb‖ ≤ Q) (hSc : ‖Sc‖ ≤ Q) (hT : ‖T‖ ≤ Q) :
    ‖w • F‖ ≤ B*Q*ε/β ∧
      ‖w • Sb+wb • F‖ ≤ 2*B*Q*ε ∧
      ‖(w • T+wc • Sb)+(wb • Sc+wbc • F)‖ ≤ 4*B*Q*ε*β := by
  have hBε : 0 ≤ B*ε := mul_nonneg hB hε
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hwSmall : |w| ≤ B*ε := hw.trans (div_le_self hBε hβ)
  have hGrow : B*ε ≤ B*ε*β := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ hBε
  have hZero : ‖w • F‖ ≤ B*Q*ε/β := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hw hF (norm_nonneg _) (div_nonneg hBε hβ0)).trans_eq (by ring)
  have hFirst : ‖w • Sb+wb • F‖ ≤ 2*B*Q*ε := by
    have h0 : ‖w • Sb‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hwSmall hSb (norm_nonneg _) hBε
    have h1 : ‖wb • F‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hwb hF (norm_nonneg _) hBε
    exact ((norm_add_le _ _).trans (add_le_add h0 h1)).trans_eq (by ring)
  refine ⟨hZero,hFirst,?_⟩
  have hh := norm_second_weighted_jet_le F Sb Sc T w wb wc wbc
    (B*ε*β) Q Q Q 1 1 (mul_nonneg hBε hβ0) zero_le_one
    (hwSmall.trans hGrow) (by simpa only [mul_one] using hwb.trans hGrow)
    (by simpa only [mul_one] using hwc.trans hGrow)
    (by simpa only [one_pow,mul_one] using hwbc)
    (by simpa only [mul_one] using hF) (by simpa only [mul_one] using hSb)
    (by simpa only [mul_one] using hSc) (by simpa only [one_pow,mul_one] using hT)
  exact hh.trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
