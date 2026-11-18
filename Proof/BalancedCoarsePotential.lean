import Proof.ActualRadialTaylorEndpoints
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Canonical balanced realization of an angular-order-one coarse coefficient. -/
def balancedCoarsePotentialL (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
    (T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))

lemma norm_balancedCoarsePotentialL_le (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    ‖balancedCoarsePotentialL T‖ ≤ ‖T‖ := by
  have hT : ‖T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))‖ ≤ ‖T‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg T)).trans_eq (mul_one _))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_sphereSobolevInclusionL_le _ _ _) hT
      (norm_nonneg (T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))) zero_le_one).trans_eq (one_mul _))

lemma balancedCoarsePotentialL_actual (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (u : SphereSobolev 2) :
    balancedCoarsePotentialL T (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (T (sphereSobolevInclusionL 2 1 (by norm_num) u)) := by
  simp only [balancedCoarsePotentialL,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply]
end ShrinkingSpheres
