import Proof.ScalarOperatorInverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres

/-- A half-unit norm neighborhood of the identity provides both genuine
    invertibility and the canonical inverse bound. -/
theorem near_identity_inverse_data {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E)
    (hNear : ‖A-ContinuousLinearMap.id ℝ E‖ ≤ (1/2:ℝ)) :
    A.IsInvertible ∧ ‖A.inverse‖ ≤ 2 := by
  have hSmall : ‖(1:E →L[ℝ] E)-A‖ < 1 := by
    rw [norm_sub_rev]
    exact hNear.trans_lt (by norm_num)
  obtain ⟨u,hu⟩ := isUnit_one_sub_of_norm_lt_one (R:=E →L[ℝ] E) hSmall
  have huA : (u : E →L[ℝ] E) = A := hu.trans (by abel)
  have hRight : A.comp (u⁻¹).val = ContinuousLinearMap.id ℝ E := by
    rw [← huA]
    exact u.val_inv
  have hLeft : (u⁻¹).val.comp A = ContinuousLinearMap.id ℝ E := by
    rw [← huA]
    exact u.inv_val
  have hA := ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft
  obtain ⟨hId,hIdNorm⟩ := scalar_identity_inverse_data E 1 (by norm_num)
  have hBound := inverse_norm_le_twice_of_half_perturbation A
    ((1:ℝ) • ContinuousLinearMap.id ℝ E) hA hId 1 (by norm_num)
    (by simpa only [inv_one] using hIdNorm) (by simpa only [one_smul,one_mul] using hNear)
  exact ⟨hA,by simpa only [mul_one] using hBound⟩

end ShrinkingSpheres
