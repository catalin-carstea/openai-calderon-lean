import Proof.RightMultiplierRotationGraph
import Proof.ClosedCoefficientAngularGenerators
import Proof.CoarseDegreeCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

structure ScalarRotationMultiplierData where
  one : SphereSobolev 1 →L[ℝ] SphereSobolev 1
  coarse : SphereSobolev 0 →L[ℝ] SphereSobolev 0
  angularOne : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 1
  angularCoarse : I × I → SphereSobolev 0 →L[ℝ] SphereSobolev 0
  compatible : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (one u) =
    coarse (sphereSobolevInclusionL 1 0 (by norm_num) u)
  symmetric : ∀ u v,⟪coarse u,v⟫_ℝ = ⟪u,coarse v⟫_ℝ
  angularCompatible : ∀ ij u,sphereSobolevInclusionL 1 0 (by norm_num) (angularOne ij u) =
    angularCoarse ij (sphereSobolevInclusionL 1 0 (by norm_num) u)
  angularSymmetric : ∀ ij u v,⟪angularCoarse ij u,v⟫_ℝ = ⟪u,angularCoarse ij v⟫_ℝ
  product : ∀ ij u,sphereSobolevRotationL 1 ij.1 ij.2 (one u) =
    angularCoarse ij (sphereSobolevInclusionL 1 0 (by norm_num) u)+coarse (sphereSobolevRotationL 1 ij.1 ij.2 u)

def scalarRotationDataOfClosedCoefficient
    (Q : OAI.AnisotropicCalderon.DirichletFamily.ClosedCoefficientJets 3) : ScalarRotationMultiplierData where
  one := closedOneBoundaryScalarMultiplierL Q
  coarse := closedThreeJetCoarseScalarMultiplierL Q
  angularOne ij := closedCoefficientAngularOneL ij.1 ij.2 Q
  angularCoarse ij := closedCoefficientAngularCoarseL ij.1 ij.2 Q
  compatible := closedThreeJet_scalar_multiplier_compatible Q
  symmetric := closedThreeJetCoarseScalarMultiplierL_symmetric Q
  angularCompatible ij := closedCoefficientAngular_compatible ij.1 ij.2 Q
  angularSymmetric ij := closedCoefficientAngularCoarseL_symmetric ij.1 ij.2 Q
  product ij := closedCoefficientMultiplier_rotation_product ij.1 ij.2 Q

structure CoarseRotationAdjointPacket where
  operator : SphereSobolev 1 →L[ℝ] SphereSobolev 0
  adjoint : SphereSobolev 1 →L[ℝ] SphereSobolev 0
  angular : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  angularAdjoint : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  pairing : ∀ u v,⟪operator u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,adjoint v⟫_ℝ
  graph : ∀ ij,∀ f : SphereSobolev 2,
    sphereSobolevRotationL 0 ij.1 ij.2 (operator (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (angular ij (sphereSobolevInclusionL 2 1 (by norm_num) f)+operator (sphereSobolevRotationL 2 ij.1 ij.2 f))
  angularPairing : ∀ ij u v,⟪angular ij u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,angularAdjoint ij v⟫_ℝ

namespace CoarseRotationAdjointPacket

def data (P : CoarseRotationAdjointPacket) : CoarseDegreeCompatibility.CoarseDegreeData :=
  (P.operator,(P.angular,P.angularAdjoint))

lemma data_mem (P : CoarseRotationAdjointPacket) : P.data ∈ CoarseDegreeCompatibility.compatibleData := by
  apply (CoarseDegreeCompatibility.mem_compatibleData_iff _).mpr
  exact ⟨fun ij m n z => coarsePhysicalHarmonicBlock_of_rotation_distribution ij.1 ij.2
    P.operator (P.angular ij) (P.graph ij) m n z,P.angularPairing⟩

/-- Right scalar multiplication preserves actual coarse rotation graphs
    and both true adjunctions, with explicit shared witnesses. -/
def mulRight (P : CoarseRotationAdjointPacket) (Q : ScalarRotationMultiplierData) : CoarseRotationAdjointPacket where
  operator := P.operator.comp Q.one
  adjoint := Q.coarse.comp P.adjoint
  angular ij := (P.angular ij).comp Q.one+P.operator.comp (Q.angularOne ij)
  angularAdjoint ij := Q.coarse.comp (P.angularAdjoint ij)+(Q.angularCoarse ij).comp P.adjoint
  pairing := coarse_pairing_comp_right_multiplier P.operator P.adjoint Q.one Q.coarse P.pairing Q.compatible Q.symmetric
  graph ij := coarse_rotation_graph_comp_right_multiplier ij.1 ij.2 P.operator (P.angular ij) (P.graph ij)
    Q.one (Q.angularOne ij) Q.coarse (Q.angularCoarse ij) Q.compatible (Q.angularCompatible ij) (Q.product ij)
  angularPairing := by
    intro ij u v
    have hFirst := coarse_pairing_comp_right_multiplier (P.angular ij) (P.angularAdjoint ij)
      Q.one Q.coarse (P.angularPairing ij) Q.compatible Q.symmetric u v
    have hSecond := coarse_pairing_comp_right_multiplier P.operator P.adjoint
      (Q.angularOne ij) (Q.angularCoarse ij) P.pairing (Q.angularCompatible ij) (Q.angularSymmetric ij) u v
    change ⟪P.angular ij (Q.one u)+P.operator (Q.angularOne ij u),sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Q.coarse (P.angularAdjoint ij v)+Q.angularCoarse ij (P.adjoint v)⟫_ℝ
    exact (inner_add_left _ _ _).trans ((congrArg₂ (fun a b : ℝ => a+b) hFirst hSecond).trans (inner_add_right _ _ _).symm)

end CoarseRotationAdjointPacket
end ShrinkingSpheres
