import Proof.ScalarOperatorInverse
import Proof.PoissonFirstVariationBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
namespace ShrinkingSpheres

theorem scalar_identity_inverse_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : c ≠ 0) :
    (c • ContinuousLinearMap.id ℝ E).inverse = c⁻¹ • ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.inverse_eq
  · apply ContinuousLinearMap.ext
    intro x
    change c • (c⁻¹ • x) = x
    rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
  · apply ContinuousLinearMap.ext
    intro x
    change c⁻¹ • (c • x) = x
    rw [smul_smul,inv_mul_cancel₀ hc,one_smul]

/-- Affine Taylor inversion with the actual inverse. No differentiable
    parameter extension is needed, and all bounds use shared operators. -/
theorem norm_scalar_inverse_affine_remainder_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A A1 : E →L[ℝ] E) (c r C D P Q : ℝ) (hc : 0 < c) (hr : 0 ≤ r)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : A.IsInvertible) (hInv : ‖A.inverse‖ ≤ C)
    (hDiff : ‖A-c • ContinuousLinearMap.id ℝ E‖ ≤ D*r)
    (hFirst : ‖A1‖ ≤ P)
    (hRem : ‖A-c • ContinuousLinearMap.id ℝ E-r • A1‖ ≤ Q*r^2) :
    ‖A.inverse-c⁻¹ • ContinuousLinearMap.id ℝ E+r • ((c⁻¹)^2 • A1)‖ ≤
      C*(c⁻¹*Q+(c⁻¹)^2*D*P)*r^2 := by
  let A0 : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  let B : E →L[ℝ] E := c⁻¹ • ContinuousLinearMap.id ℝ E
  let R := A-A0-r • A1
  have hb : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  obtain ⟨hA0,hInv0⟩ := scalar_identity_inverse_data E c hc
  have hInvEq : A0.inverse = B := scalar_identity_inverse_eq E c hc.ne'
  have hIB : ‖A.inverse-B‖ ≤ C*(D*r)*c⁻¹ := by
    have ht := norm_inverse_sub_le A A0 hA hA0 C c⁻¹ (D*r) hC hb (mul_nonneg hD hr) hInv hInv0 hDiff
    have hn := congrArg (fun T : E →L[ℝ] E => ‖A.inverse-T‖) hInvEq
    exact hn.symm.le.trans ht
  have hEq : A.inverse-B+r • ((c⁻¹)^2 • A1) =
      -(c⁻¹ • A.inverse.comp R)-r • (c⁻¹ • (A.inverse-B).comp A1) := by
    apply ContinuousLinearMap.ext
    intro x
    have hCancel : c⁻¹ • (c • A.inverse x) = A.inverse x := by
      rw [smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
    simp only [R,A0,B,_root_.add_apply,_root_.sub_apply,_root_.neg_apply,_root_.smul_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_sub,map_smul,
      hA.inverse_apply_self,smul_sub,hCancel]
    module
  have hR : ‖c⁻¹ • A.inverse.comp R‖ ≤ c⁻¹*C*(Q*r^2) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hb]
    exact (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hInv hRem (norm_nonneg _) hC)) hb).trans_eq (by ring)
  have hS : ‖c⁻¹ • (A.inverse-B).comp A1‖ ≤ c⁻¹*(C*(D*r)*c⁻¹)*P := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hb]
    exact (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hIB hFirst (norm_nonneg _) (by positivity))) hb).trans_eq (by ring)
  have hScale : ‖r • (c⁻¹ • (A.inverse-B).comp A1)‖ = r*‖c⁻¹ • (A.inverse-B).comp A1‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  exact (congrArg norm hEq).le.trans ((norm_sub_le _ _).trans (by
    rw [norm_neg,hScale]
    exact (add_le_add hR (mul_le_mul_of_nonneg_left hS hr)).trans_eq (by ring)))

end ShrinkingSpheres
