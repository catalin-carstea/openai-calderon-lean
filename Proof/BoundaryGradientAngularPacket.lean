import Proof.CoarseAngularPacketLinearity
import Proof.CoordinateScalarRotationPacket
import Proof.RotationCoarseAdjointPacket
import Proof.ClosedBoundaryGradientAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Factor each vector coefficient through one common first order packet.
    Multiplication uses its actual closed C3 realization. -/
def boundaryGradientAdjointCoarsePacket (Q : I → ClosedCoefficientJets 3)
    (P : CoarseRotationAdjointPacket) : CoarseRotationAdjointPacket :=
  CoarseRotationAdjointPacket.sum (fun j : I =>
    ((CoarseRotationAdjointPacket.sum (fun i : I =>
      ((rotationCoarseAdjointPacket i j).mulRight (coordinateScalarRotationData i)).smul (-1))).add
        (P.mulRight (coordinateScalarRotationData j))).mulRight (scalarRotationDataOfClosedCoefficient (Q j)))

theorem boundaryGradientAdjointCoarsePacket_operator (Q : I → ClosedCoefficientJets 3)
    (P : CoarseRotationAdjointPacket) :
    (boundaryGradientAdjointCoarsePacket Q P).operator = closedBoundaryGradientAdjoint Q P.operator := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [boundaryGradientAdjointCoarsePacket,CoarseRotationAdjointPacket.sum,
    CoarseRotationAdjointPacket.add,CoarseRotationAdjointPacket.smul,CoarseRotationAdjointPacket.mulRight,
    rotationCoarseAdjointPacket,coordinateScalarRotationData,scalarRotationDataOfClosedCoefficient,
    closedBoundaryGradientAdjoint,closedVectorTangentialAdjoint,closedVectorNormalMultiplier,
    _root_.sum_apply,_root_.add_apply,_root_.neg_apply,ContinuousLinearMap.comp_apply,map_sum,map_add,map_neg,
    ContinuousLinearMap.comp_assoc,neg_one_smul,Finset.sum_add_distrib]

/-- This packet already lies in the closed domain of the degree-commutator
    extractor; no unproved endpoint multiplier premise is introduced. -/
theorem boundaryGradientAdjointCoarsePacket_compatible (Q : I → ClosedCoefficientJets 3)
    (P : CoarseRotationAdjointPacket) :
    (boundaryGradientAdjointCoarsePacket Q P).data ∈ CoarseDegreeCompatibility.compatibleData :=
  (boundaryGradientAdjointCoarsePacket Q P).data_mem

end ShrinkingSpheres
