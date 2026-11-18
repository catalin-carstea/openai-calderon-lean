import Proof.CoarseAngularProductPackets
import Proof.RotationDistributionFromBlocks
import Proof.RadialCorrectionRotationCommutator
import Proof.RadialRotationCommutator
import Proof.FlatDegreeCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

def degreeCoarseAdjointPacket : CoarseRotationAdjointPacket where
  operator := sphereSobolevDegreeL
  adjoint := sphereSobolevDegreeL
  angular _ := 0
  angularAdjoint _ := 0
  pairing := sphereSobolevDegreeL_symmetric
  graph := by
    intro ij f
    apply rotation_distribution_of_physical_blocks ij.1 ij.2 sphereSobolevDegreeL 0
    intro m n z
    change sphereSobolevCoefficientL 0 m (0 : SphereSobolev 0) =
      harmonicSphereRotation m ij.1 ij.2
        (sphereSobolevCoefficientL 0 m (sphereSobolevDegreeL (sphereSobolevSingleL 1 n z)))-
        sphereSobolevCoefficientL 0 m (sphereSobolevDegreeL
          (sphereSobolevSingleL 1 n (harmonicSphereRotation n ij.1 ij.2 z)))
    by_cases hmn : m=n
    · subst m
      simp only [map_zero,sphereSobolevDegreeL_single,map_smul,sphereSobolevCoefficientL_single_self,sub_self]
    · simp only [map_zero,sphereSobolevDegreeL_single,map_smul,sphereSobolevCoefficientL_single_ne _ _ _ hmn,smul_zero,sub_self]
  angularPairing := by
    intro ij u v
    simp only [_root_.zero_apply,inner_zero_left,inner_zero_right]

/-- The first covector model and its true adjoint, including the actual
    commutators with every rotation generator. -/
def firstRadialAdjointCoarsePacket (ell : X →L[ℝ] ℝ) : CoarseRotationAdjointPacket where
  operator := (radialCorrectionCovectorL ell).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))
  adjoint := (radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))
  angular ij := (radialCorrectionCovectorL (rotationCovector ell ij.1 ij.2)).adjoint.comp
    (sphereSobolevInclusionL 1 0 (by norm_num))
  angularAdjoint ij := (radialCorrectionCovectorL (rotationCovector ell ij.1 ij.2)).comp
    (sphereSobolevInclusionL 1 0 (by norm_num))
  pairing := by
    intro u v
    exact ContinuousLinearMap.adjoint_inner_left (radialCorrectionCovectorL ell)
      (sphereSobolevInclusionL 1 0 (by norm_num) v)
      (sphereSobolevInclusionL 1 0 (by norm_num) u)
  graph := by
    intro ij f
    change sphereSobolevRotationL 0 ij.1 ij.2
      ((radialCorrectionCovectorL ell).adjoint (sphereSobolevInclusionL 1 0 (by norm_num)
        (sphereSobolevInclusionL 2 1 (by norm_num) f))) = _
    exact first_radial_rotation_commutator_distribution ij.1 ij.2
      (radialCorrectionCovectorL ell).adjoint
      (radialCorrectionCovectorL (rotationCovector ell ij.1 ij.2)).adjoint
      (radialCorrectionAdjointSobolevL 1 ell)
      (radialCorrectionAdjointSobolevL_coarse ell)
      (rotation_radialCorrectionAdjoint_commutator ij.1 ij.2 ell) f
  angularPairing := by
    intro ij u v
    exact ContinuousLinearMap.adjoint_inner_left
      (radialCorrectionCovectorL (rotationCovector ell ij.1 ij.2))
      (sphereSobolevInclusionL 1 0 (by norm_num) v)
      (sphereSobolevInclusionL 1 0 (by norm_num) u)

end ShrinkingSpheres
