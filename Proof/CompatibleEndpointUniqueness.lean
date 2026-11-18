import Proof.SphereSobolevOperatorExt
import Proof.DenseOperatorRestrictionUnique
import Proof.NativeFullHalfResponse
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma half_endpoint_unique_of_coarse
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L H : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hH : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      H.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) : L=H := by
  have hEq := hL.symm.trans hH
  exact clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) L H hEq

lemma higher_endpoint_unique_of_coarse
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hL : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp L =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hH : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) : L=H := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  exact congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T u) (hL.trans hH.symm)
end ShrinkingSpheres
