import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres

lemma norm_finite_mixed_quadratic_words_le_mass
    {ι E F G : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : ι → ι → ℝ) (Lo : ι → F →L[ℝ] G) (Hi : ι → E →L[ℝ] F)
    (w : ι → ℝ) {BA BH : ℝ} (hBA : 0 ≤ BA) (hBH : 0 ≤ BH) (hw : ∀ a,0 ≤ w a)
    (hL : ∀ a,‖Lo a‖ ≤ BA*w a) (hH : ∀ a,‖Hi a‖ ≤ BH*w a) :
    ‖∑ a,∑ b,c a b • (Lo a).comp (Hi b)‖ ≤ (BA*BH)*(∑ a,∑ b,|c a b| *w a*w b) := by
  have hTerm (a b : ι) : ‖c a b • (Lo a).comp (Hi b)‖ ≤ (BA*BH)*(|c a b| *w a*w b) := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |c a b| *(‖Lo a‖*‖Hi b‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (abs_nonneg _)
      _ ≤ |c a b| *((BA*w a)*(BH*w b)) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hL a) (hH b) (norm_nonneg _) (mul_nonneg hBA (hw a))) (abs_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ a,∑ b,‖c a b • (Lo a).comp (Hi b)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
    _ ≤ ∑ a,∑ b,(BA*BH)*(|c a b| *w a*w b) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hTerm a b))
    _ = _ := by simp only [Finset.mul_sum]

end ShrinkingSpheres
