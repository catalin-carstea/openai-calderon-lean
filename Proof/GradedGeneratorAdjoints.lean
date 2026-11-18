import Proof.HalfPhysicalAdjoint
import Proof.NativeFullHalfResponse
import Proof.ShiftedDegreeInclusion
import Proof.RotationCoarseAdjointPacket
import Proof.HalfBoundaryGradientAdjoint
import Proof.CompatibleEndpointUniqueness
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A physical coarse adjunction identifies the genuine dual-half transpose
of any compatible low endpoint; no new adjoint witness is chosen. -/
lemma half_endpoint_adjoint_of_coarse_pair
    (R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L La : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ)
    (hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R=
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hLa : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp Ra=
      La.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) : L.adjoint=La := by
  have hBlocks := half_physical_blocks_of_coarse_compatible R L hL
  have hAdj := half_coarse_compatible_of_physical_blocks Ra L.adjoint
    (half_operator_adjoint_physical_block R Ra hPair L hBlocks)
  exact half_endpoint_unique_of_coarse Ra L.adjoint La hAdj hLa

lemma sphereSobolevShiftedDegreeHalf_adjoint :
    (sphereSobolevShiftedDegreeL (1/2:ℝ)).adjoint=sphereSobolevShiftedDegreeL (1/2:ℝ) := by
  have hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp sphereSobolevDegreeL=
      (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) :=
    ContinuousLinearMap.ext sphereSobolevDegreeL_half
  exact half_endpoint_adjoint_of_coarse_pair _ _ _ _ sphereSobolevDegreeL_symmetric hL hL

lemma sphereSobolevRotationHalf_adjoint (i j : I) :
    (sphereSobolevRotationL (1/2:ℝ) i j).adjoint= -sphereSobolevRotationL (1/2:ℝ) i j := by
  have hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (sphereSobolevRotationL 1 i j)=
      (sphereSobolevRotationL (1/2:ℝ) i j).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) :=
    ContinuousLinearMap.ext (oneRotation_half_inclusion i j)
  have hLa : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (-sphereSobolevRotationL 1 i j)=
      (-sphereSobolevRotationL (1/2:ℝ) i j).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    simpa only [ContinuousLinearMap.comp_neg,ContinuousLinearMap.neg_comp] using congrArg Neg.neg hL
  exact half_endpoint_adjoint_of_coarse_pair _ _ _ _ (rotationCoarseAdjointPacket i j).pairing hL hLa
end ShrinkingSpheres
