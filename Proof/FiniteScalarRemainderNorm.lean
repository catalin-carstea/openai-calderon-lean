import Proof.FiniteScalarRemainderNorms
import Proof.TaylorScalarAdjointRemainderBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ShrinkingSpheres

lemma norm_finite_scalar_remainder_weighted {κ Q E : Type*} [Fintype κ]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Q →L[ℝ] (E →L[ℝ] E)) (K C : κ → E →L[ℝ] E)
    (q : κ → Q) (w sign : κ → ℝ) (CK CC : ℝ)
    (hSign : ∀ a,|sign a|=1) (hK : ∀ a,‖K a‖ ≤ CK*w a)
    (hC : ∀ a,‖C a‖ ≤ CC*(w a*‖q a‖)) :
    ‖∑ a,((M (q a)).comp (K a)-sign a • C a)‖ ≤
      (‖M‖*CK+CC)*(∑ a,w a*‖q a‖) := by
  have hSum := norm_finite_scalar_remainder_le M K C q sign hSign
  apply hSum.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hKN := mul_le_mul_of_nonneg_left (hK a) (mul_nonneg (norm_nonneg M) (norm_nonneg (q a)))
  exact (add_le_add hKN (hC a)).trans_eq (by ring)
end ShrinkingSpheres
