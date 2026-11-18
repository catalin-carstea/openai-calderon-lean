import Mathlib.Analysis.Normed.Operator.Bilinear
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
/-- Shared two-sided composition estimate used by diagonal and full-matrix
    actual raising/error coefficients. -/
lemma norm_bounded_composition_cross_le (A L : V →L[ℝ] W) (B H : U →L[ℝ] V)
    {CA CB q : ℝ} (hCA : 0 ≤ CA) (hq : 0 ≤ q)
    (hA : ‖A‖ ≤ CA) (hB : ‖B‖ ≤ CB) (hL : ‖L‖ ≤ q) (hH : ‖H‖ ≤ q) :
    ‖A.comp H+L.comp B‖ ≤ (CA+CB)*q := by
  calc
    _ ≤ ‖A.comp H‖+‖L.comp B‖ := norm_add_le _ _
    _ ≤ ‖A‖*‖H‖+‖L‖*‖B‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ CA*q+q*CB := add_le_add (mul_le_mul hA hH (norm_nonneg _) hCA)
      (mul_le_mul hL hB (norm_nonneg _) hq)
    _ = _ := by ring
end ShrinkingSpheres
