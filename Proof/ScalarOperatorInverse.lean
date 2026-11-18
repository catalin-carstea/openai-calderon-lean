import Proof.InversePerturbation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 15
namespace ShrinkingSpheres

/-- The scalar identity has the exact reciprocal inverse and its uniform norm bound. -/
theorem scalar_identity_inverse_data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : 0 < c) :
    (c • ContinuousLinearMap.id ℝ E).IsInvertible ∧
      ‖(c • ContinuousLinearMap.id ℝ E).inverse‖ ≤ c⁻¹ := by
  let A : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  let R : E →L[ℝ] E := c⁻¹ • ContinuousLinearMap.id ℝ E
  have hRight : A.comp R = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro x
    change c • (c⁻¹ • x) = x
    rw [smul_smul,mul_inv_cancel₀ hc.ne',one_smul]
  have hLeft : R.comp A = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro x
    change c⁻¹ • (c • x) = x
    rw [smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
  have hInv := ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft
  have hEq : A.inverse = R := ContinuousLinearMap.inverse_eq hRight hLeft
  have hNorm : ‖R‖ ≤ c⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    intro x
    change ‖c⁻¹ • x‖ ≤ c⁻¹*‖x‖
    simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)] using norm_smul_le c⁻¹ x
  exact ⟨hInv,(congrArg norm hEq).le.trans hNorm⟩

end ShrinkingSpheres
