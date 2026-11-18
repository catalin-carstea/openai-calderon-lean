import Proof.CoarseDegreeCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarseDegreeCommutator_add
    (R T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    coarseDegreeCommutator (R+T) = coarseDegreeCommutator R+coarseDegreeCommutator T := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevShiftedDegreeL 0 ((R+T) (sphereSobolevInclusionL 2 1 (by norm_num) u))-
    sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) ((R+T) (sphereSobolevShiftedDegreeL 2 u)) =
    (sphereSobolevShiftedDegreeL 0 (R (sphereSobolevInclusionL 2 1 (by norm_num) u))-
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) (R (sphereSobolevShiftedDegreeL 2 u)))+
    (sphereSobolevShiftedDegreeL 0 (T (sphereSobolevInclusionL 2 1 (by norm_num) u))-
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) (T (sphereSobolevShiftedDegreeL 2 u)))
  simp only [_root_.add_apply,map_add]
  abel

lemma coarseDegreeCommutator_smul
    (c : ℝ) (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    coarseDegreeCommutator (c • R) = c • coarseDegreeCommutator R := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevShiftedDegreeL 0 ((c • R) (sphereSobolevInclusionL 2 1 (by norm_num) u))-
    sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) ((c • R) (sphereSobolevShiftedDegreeL 2 u)) =
    c • (sphereSobolevShiftedDegreeL 0 (R (sphereSobolevInclusionL 2 1 (by norm_num) u))-
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) (R (sphereSobolevShiftedDegreeL 2 u)))
  simp only [_root_.smul_apply,map_smul,smul_sub]

end ShrinkingSpheres
