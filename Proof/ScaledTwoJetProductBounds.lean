import Proof.CoarseCovariantSecondProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Sharp small scalar jets cancel the beta growth of the actual bounded
correction's covariant jets in the four genuine product-rule terms. -/
lemma scaled_two_jet_product_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F Sb Sc T : E)
    (w wb wc wbc B C ε β : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hw : |w| ≤ B*ε/β^2) (hwb : |wb| ≤ B*ε/β) (hwc : |wc| ≤ B*ε/β)
    (hwbc : |wbc| ≤ B*ε)
    (hF : ‖F‖ ≤ C) (hSb : ‖Sb‖ ≤ C*β) (hSc : ‖Sc‖ ≤ C*β) (hT : ‖T‖ ≤ C*β^2) :
    ‖w • F‖ ≤ B*C*ε/β^2 ∧
      ‖w • Sb+wb • F‖ ≤ 2*B*C*ε/β ∧
      ‖(w • T+wc • Sb)+(wb • Sc+wbc • F)‖ ≤ 4*B*C*ε := by
  have hBε : 0 ≤ B*ε := mul_nonneg hB hε
  have h0 : ‖w • F‖ ≤ (B*ε/β^2)*C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hw hF (norm_nonneg _) (by positivity)
  have h1 : ‖w • Sb‖ ≤ (B*ε/β^2)*(C*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hw hSb (norm_nonneg _) (by positivity)
  have h2 : ‖wb • F‖ ≤ (B*ε/β)*C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwb hF (norm_nonneg _) (by positivity)
  have h20 : ‖w • T‖ ≤ (B*ε/β^2)*(C*β^2) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hw hT (norm_nonneg _) (by positivity)
  have h21 : ‖wc • Sb‖ ≤ (B*ε/β)*(C*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwc hSb (norm_nonneg _) (by positivity)
  have h22 : ‖wb • Sc‖ ≤ (B*ε/β)*(C*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwb hSc (norm_nonneg _) (by positivity)
  have h23 : ‖wbc • F‖ ≤ (B*ε)*C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwbc hF (norm_nonneg _) hBε
  refine ⟨h0.trans_eq (by ring),?_,?_⟩
  · have hFirst : ‖w • Sb+wb • F‖ ≤ (B*ε/β^2)*(C*β)+(B*ε/β)*C :=
      (norm_add_le _ _).trans (add_le_add h1 h2)
    exact hFirst.trans_eq (by field_simp;ring)
  · have hSecond : ‖(w • T+wc • Sb)+(wb • Sc+wbc • F)‖ ≤
        ((B*ε/β^2)*(C*β^2)+(B*ε/β)*(C*β))+((B*ε/β)*(C*β)+(B*ε)*C) :=
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))).trans
        (add_le_add (add_le_add h20 h21) (add_le_add h22 h23))
    exact hSecond.trans_eq (by field_simp;ring)

end ShrinkingSpheres
