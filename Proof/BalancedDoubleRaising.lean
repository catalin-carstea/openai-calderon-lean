import Proof.FrameErrorRaisingHalfCross
import Proof.FlatRaisingCoarseRotation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma flatOneRaisingL_zero_coarse (i : I) (v : SphereSobolev 1) :
    flatZeroRaisingL i (sphereSobolevInclusionL 1 0 (by norm_num) v)=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) (flatOneRaisingL i v) := by
  have hh := flatRaisingSobolevL_inclusion 1 0 (by norm_num) i
  have hI : sphereSobolevInclusionL ((1:ℝ)-1) ((0:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact DFunLike.congr_fun hh v

/-- The balanced double raising map is the SAME actual H2-to-L2 double
    action after the genuine inclusion into H(-1). -/
lemma flatBalancedDoubleRaising_coarse (i j : I) (u : SphereSobolev 2) :
    sphereSobolevInclusionL (-(1/2:ℝ)) (-1:ℝ) (by norm_num)
      (flatHalfRaisingL i (flatThreeHalfRaisingL j (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)))=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) (flatOneRaisingL i (flatTwoRaisingL j u)) := by
  have hL := DFunLike.congr_fun (flatHalfRaisingL_coarse i)
    (flatThreeHalfRaisingL j (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u))
  have hH := DFunLike.congr_fun (flatThreeHalfRaisingL_high j) u
  simp only [ContinuousLinearMap.comp_apply] at hL hH
  rw [hL,hH,sphereSobolevInclusionL_trans_apply,flatOneRaisingL_zero_coarse]
end ShrinkingSpheres
