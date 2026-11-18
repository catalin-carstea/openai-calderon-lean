import Proof.FlatRaisingCoordinateRotation
import Proof.FlatRaisingZeroOrder
import Proof.FrameErrorMatrixRaisingCross
import Proof.ShiftedDegreeInclusion
import Proof.HalfBoundaryGradientAdjoint
import Proof.Archive.SphereSobolevConormalRotationDerivative
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The reordered raising formula on the true balanced domain. Rotations
    and degree act before multipliers, and the final term has angular order zero. -/
lemma flatHalfRaising_coordinate_rotation (i : I) :
    flatHalfRaisingL i=
      -(∑ k : I,(coordinateMultiplierSobolevL (-(1/2:ℝ)) k).comp (sphereSobolevRotationL (1/2:ℝ) k i))+
      (coordinateMultiplierSobolevL (-(1/2:ℝ)) i).comp (sphereSobolevShiftedDegreeL (1/2:ℝ))+
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (flatRaisingZeroOrderL (1/2:ℝ) i) := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  have hMul (k : I) (w : SphereSobolev 0) :
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (coordinateMultiplierSobolevL 0 k w)=
        coordinateMultiplierSobolevL (-(1/2:ℝ)) k (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) w) :=
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics 0 (-(1/2:ℝ)) (by norm_num) (axis k) w
  have hRot (k : I) :
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevRotationL 1 k i u)=
        sphereSobolevRotationL (1/2:ℝ) k i (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) := by
    exact oneRotation_half_inclusion k i u
  have hA := flatOneRaisingL_half i u
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (flatRaisingSobolevL 1 i u)=
    flatHalfRaisingL i (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) at hA
  have h := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
    (flatRaising_coordinate_rotation i u)
  rw [hA,← flatRaisingZeroOrderL_zero i] at h
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.neg_apply,_root_.sum_apply,
    map_add,map_neg,map_sum,hMul,hRot,sphereSobolevDegreeL_half,
    flatRaisingZeroOrderL_inclusion,sphereSobolevInclusionL_trans_apply] at h ⊢
  exact h

/-- The SAME reordered identity at the higher endpoint used in actual
    error/raising products. -/
lemma flatThreeHalfRaising_coordinate_rotation (i : I) :
    flatThreeHalfRaisingL i=
      -(∑ k : I,(coordinateMultiplierSobolevL (1/2:ℝ) k).comp (sphereSobolevRotationL (3/2:ℝ) k i))+
      (coordinateMultiplierSobolevL (1/2:ℝ) i).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))+
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (flatRaisingZeroOrderL (3/2:ℝ) i) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  have hMul (k : I) (w : SphereSobolev (1/2:ℝ)) :
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (coordinateMultiplierSobolevL (1/2:ℝ) k w)=
        coordinateMultiplierSobolevL (-(1/2:ℝ)) k
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) w) :=
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (axis k) w
  have hRot (k : I) :
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (sphereSobolevRotationL (3/2:ℝ) k i u)=
        sphereSobolevRotationL (1/2:ℝ) k i (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) := by
    have h := sphereSobolevRotationL_inclusion (3/2:ℝ) (1/2:ℝ) (by norm_num) k i
    rw [hI] at h
    exact (DFunLike.congr_fun h u).symm
  have hD := sphereSobolevShiftedDegreeL_inclusion (3/2:ℝ) (1/2:ℝ) (by norm_num) u
  rw [hI] at hD
  have hA : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (flatThreeHalfRaisingL i u)=
      flatHalfRaisingL i (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) := by
    have h := flatRaisingSobolevL_inclusion (3/2:ℝ) (1/2:ℝ) (by norm_num) i
    rw [hI] at h
    exact (DFunLike.congr_fun h u).symm
  have h := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    T (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))
    (flatHalfRaising_coordinate_rotation i)
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.neg_apply,_root_.sum_apply,
    map_add,map_neg,map_sum,hMul,hRot,hD,hA,
    flatRaisingZeroOrderL_inclusion,sphereSobolevInclusionL_trans_apply] at h ⊢
  exact h
end ShrinkingSpheres
