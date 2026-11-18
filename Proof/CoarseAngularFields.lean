import Proof.CoarseAngularPacketLinearity
import Proof.BoundaryGradientAngularPacket
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open scoped BigOperators
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Proof-free operator fields allow one smooth family to be used on an open
    domain, while its actual graph proofs are supplied pointwise. -/
structure CoarseAngularFields where
  operator : SphereSobolev 1 →L[ℝ] SphereSobolev 0
  adjoint : SphereSobolev 1 →L[ℝ] SphereSobolev 0
  angular : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  angularAdjoint : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0

namespace CoarseAngularFields

def ofPacket (P : CoarseRotationAdjointPacket) : CoarseAngularFields :=
  ⟨P.operator,P.adjoint,P.angular,P.angularAdjoint⟩

def smul (c : ℝ) (P : CoarseAngularFields) : CoarseAngularFields :=
  ⟨c • P.operator,c • P.adjoint,(fun ij => c • P.angular ij),(fun ij => c • P.angularAdjoint ij)⟩
def add (P Q : CoarseAngularFields) : CoarseAngularFields :=
  ⟨P.operator+Q.operator,P.adjoint+Q.adjoint,(fun ij => P.angular ij+Q.angular ij),
    (fun ij => P.angularAdjoint ij+Q.angularAdjoint ij)⟩
def sum {κ : Type*} [Fintype κ] (P : κ → CoarseAngularFields) : CoarseAngularFields :=
  ⟨(∑ k,(P k).operator),(∑ k,(P k).adjoint),(fun ij => ∑ k,(P k).angular ij),
    (fun ij => ∑ k,(P k).angularAdjoint ij)⟩
def mulRight (P : CoarseAngularFields) (Q : ScalarRotationMultiplierData) : CoarseAngularFields :=
  ⟨P.operator.comp Q.one,Q.coarse.comp P.adjoint,
    (fun ij => (P.angular ij).comp Q.one+P.operator.comp (Q.angularOne ij)),
    (fun ij => Q.coarse.comp (P.angularAdjoint ij)+(Q.angularCoarse ij).comp P.adjoint)⟩

def gradient (Q : I → ClosedCoefficientJets 3) (P : CoarseAngularFields) : CoarseAngularFields :=
  sum (fun j : I =>
    ((sum (fun i : I =>
      ((ofPacket (rotationCoarseAdjointPacket i j)).mulRight (coordinateScalarRotationData i)).smul (-1))).add
        (P.mulRight (coordinateScalarRotationData j))).mulRight (scalarRotationDataOfClosedCoefficient (Q j)))

def degreeData (P : CoarseAngularFields) : CoarseDegreeCompatibility.CoarseDegreeData :=
  (P.operator,(P.angular,P.angularAdjoint))

lemma ofPacket_smul (c : ℝ) (P : CoarseRotationAdjointPacket) :
    ofPacket (P.smul c) = (ofPacket P).smul c := rfl
lemma ofPacket_add (P Q : CoarseRotationAdjointPacket) :
    ofPacket (P.add Q) = (ofPacket P).add (ofPacket Q) := rfl
lemma ofPacket_sum {κ : Type*} [Fintype κ] (P : κ → CoarseRotationAdjointPacket) :
    ofPacket (CoarseRotationAdjointPacket.sum P) = sum (fun k => ofPacket (P k)) := rfl
lemma ofPacket_mulRight (P : CoarseRotationAdjointPacket) (Q : ScalarRotationMultiplierData) :
    ofPacket (P.mulRight Q) = (ofPacket P).mulRight Q := rfl
lemma ofPacket_gradient (Q : I → ClosedCoefficientJets 3) (P : CoarseRotationAdjointPacket) :
    ofPacket (boundaryGradientAdjointCoarsePacket Q P) = gradient Q (ofPacket P) := rfl

lemma gradient_operator (Q : I → ClosedCoefficientJets 3) (P : CoarseAngularFields) :
    (gradient Q P).operator = closedBoundaryGradientAdjoint Q P.operator := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [gradient,sum,add,smul,mulRight,ofPacket,
    rotationCoarseAdjointPacket,coordinateScalarRotationData,scalarRotationDataOfClosedCoefficient,
    closedBoundaryGradientAdjoint,closedVectorTangentialAdjoint,closedVectorNormalMultiplier,
    _root_.sum_apply,_root_.add_apply,_root_.neg_apply,ContinuousLinearMap.comp_apply,map_sum,
    neg_one_smul,Finset.sum_add_distrib]

end CoarseAngularFields
end ShrinkingSpheres
