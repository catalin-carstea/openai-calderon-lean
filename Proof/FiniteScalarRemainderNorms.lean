import Mathlib.Analysis.Normed.Operator.Basic
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
/-- Shared finite scalar-reordering norm estimate at any genuine endpoint. -/
lemma norm_finite_scalar_remainder_le {E P κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype κ]
    (M : P →L[ℝ] E →L[ℝ] E) (K C : κ → E →L[ℝ] E) (Q : κ → P) (sign : κ → ℝ)
    (hSign : ∀ a,|sign a|=1) :
    ‖∑ a,((M (Q a)).comp (K a)-sign a • C a)‖ ≤
      ∑ a,((‖M‖*‖Q a‖)*‖K a‖+‖C a‖) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  have h1 := (M (Q a)).opNorm_comp_le (K a)
  have h2 := mul_le_mul_of_nonneg_right (M.le_opNorm (Q a)) (norm_nonneg (K a))
  have hh := norm_sub_le ((M (Q a)).comp (K a)) (sign a • C a)
  rw [norm_smul,Real.norm_eq_abs,hSign a,one_mul] at hh
  exact hh.trans (add_le_add (h1.trans h2) le_rfl)

/-- The same finite scalar combination estimate serves low and high
    generators, with the multiplier acting on their genuine input space. -/
lemma norm_finite_scalar_combination_weighted {E F P κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype κ]
    (G : κ → E →L[ℝ] F) (M : P →L[ℝ] E →L[ℝ] E) (Q : κ → P)
    (w : κ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ a,0 ≤ w a)
    (hG : ∀ a,‖G a‖ ≤ C*w a) :
    ‖∑ a,(G a).comp (M (Q a))‖ ≤ (C*‖M‖)*(∑ a,w a*‖Q a‖) := by
  calc
    _ ≤ ∑ a,‖(G a).comp (M (Q a))‖ := norm_sum_le _ _
    _ ≤ ∑ a,(C*‖M‖)*(w a*‖Q a‖) := by
      apply Finset.sum_le_sum
      intro a _
      exact ((G a).opNorm_comp_le _).trans
        ((mul_le_mul (hG a) (M.le_opNorm (Q a)) (norm_nonneg _) (mul_nonneg hC (hw a))).trans_eq (by ring))
    _ = _ := (Finset.mul_sum _ _ _).symm
end ShrinkingSpheres
