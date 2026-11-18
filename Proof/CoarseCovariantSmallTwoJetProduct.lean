import Proof.CoarseCovariantSecondProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Norm bounds for the SAME scalar product-rule jets with their natural
epsilon/beta, epsilon and epsilon beta weights. -/
lemma coarse_small_two_jet_product_bounds
    (F Sb Sc T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
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
  have hh := norm_coarse_second_weighted_jet_le F Sb Sc T w wb wc wbc
    (B*ε*β) Q Q Q 1 1 (mul_nonneg hBε hβ0) zero_le_one
    (hwSmall.trans hGrow) (by simpa only [mul_one] using hwb.trans hGrow)
    (by simpa only [mul_one] using hwc.trans hGrow)
    (by simpa only [one_pow,mul_one] using hwbc)
    (by simpa only [mul_one] using hF) (by simpa only [mul_one] using hSb)
    (by simpa only [mul_one] using hSc) (by simpa only [one_pow,mul_one] using hT)
  exact hh.trans_eq (by ring)

end ShrinkingSpheres
