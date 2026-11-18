import Proof.CoarseAngularFields
import Proof.RotationContractionAlgebra
import Proof.SobolevRotationIndexSkew
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

namespace CoarseAngularFields

def coordinateTangentialAdjoint (k : I) : CoarseAngularFields :=
  sum (fun a : I => ((ofPacket (rotationCoarseAdjointPacket a k)).mulRight
    (coordinateScalarRotationData a)).smul (-1))

def coordinateGradientAdjoint (P : CoarseAngularFields) (k : I) : CoarseAngularFields :=
  (coordinateTangentialAdjoint k).add (P.mulRight (coordinateScalarRotationData k))

lemma coordinateTangentialAdjoint_operator_apply (k : I) (u : SphereSobolev 1) :
    (coordinateTangentialAdjoint k).operator u =
      -(∑ a : I,sphereSobolevRotationL 1 a k (oneSphereCoordinateMulL a u)) := by
  simp only [coordinateTangentialAdjoint,sum,smul,mulRight,ofPacket,
    rotationCoarseAdjointPacket,coordinateScalarRotationData,neg_one_smul,
    _root_.sum_apply,_root_.neg_apply,ContinuousLinearMap.comp_apply]
  rw [Finset.sum_neg_distrib]

lemma coordinateTangentialAdjoint_angular_apply (k i j : I) (u : SphereSobolev 1) :
    (coordinateTangentialAdjoint k).angular (i,j) u =
      -(∑ a : I,(rotationLieCoarseL i j a k (oneSphereCoordinateMulL a u)+
        sphereSobolevRotationL 1 a k (coordinateAngularOneMul i j a u))) := by
  simp only [coordinateTangentialAdjoint,sum,smul,mulRight,ofPacket,
    rotationCoarseAdjointPacket,coordinateScalarRotationData,neg_one_smul,
    _root_.sum_apply,_root_.neg_apply,_root_.add_apply,ContinuousLinearMap.comp_apply]
  rw [Finset.sum_neg_distrib]

lemma rotationCoordinate_delta_apply (i j a k : I) (u : SphereSobolev 1) :
    rotationLieCoarseL i j a k (oneSphereCoordinateMulL a u)+
      sphereSobolevRotationL 1 a k (coordinateAngularOneMul i j a u) =
      ((if j=a then sphereSobolevRotationL 1 i k (oneSphereCoordinateMulL a u) else 0)-
        (if j=k then sphereSobolevRotationL 1 i a (oneSphereCoordinateMulL a u) else 0)-
        (if i=a then sphereSobolevRotationL 1 j k (oneSphereCoordinateMulL a u) else 0)+
        (if i=k then sphereSobolevRotationL 1 j a (oneSphereCoordinateMulL a u) else 0)+
        (if a=j then sphereSobolevRotationL 1 a k (oneSphereCoordinateMulL i u) else 0)-
        (if a=i then sphereSobolevRotationL 1 a k (oneSphereCoordinateMulL j u) else 0)) := by
  classical
  simp only [rotationLieCoarseL,coordinateAngularOneMul,_root_.add_apply,_root_.sub_apply,
    clm_ite_zero_apply,map_sub,clm_apply_ite_zero]
  abel

lemma coordinateTangentialAdjoint_angular (k i j : I) :
    (coordinateTangentialAdjoint k).angular (i,j) =
      (if k=j then (coordinateTangentialAdjoint i).operator else 0)-
        (if k=i then (coordinateTangentialAdjoint j).operator else 0) := by
  apply ContinuousLinearMap.ext
  intro u
  let v := fun p q a : I => sphereSobolevRotationL 1 p q (oneSphereCoordinateMulL a u)
  have hSkew (p q a : I) : v p q a = -v q p a :=
    congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A (oneSphereCoordinateMulL a u))
      (sphereSobolevRotationL_index_swap 1 p q)
  have hRow (l : I) : (∑ a : I,v l a a)=(coordinateTangentialAdjoint l).operator u :=
    (sum_skew_contraction v hSkew l).trans (coordinateTangentialAdjoint_operator_apply l u).symm
  have hCore := rotation_coordinate_contraction v i j k
  have hEach (a : I) := rotationCoordinate_delta_apply i j a k u
  have hLeft : (coordinateTangentialAdjoint k).angular (i,j) u =
      (if k=j then ∑ a : I,v i a a else 0)-(if k=i then ∑ a : I,v j a a else 0) := by
    rw [coordinateTangentialAdjoint_angular_apply]
    exact (congrArg Neg.neg (Finset.sum_congr rfl (fun a _ => hEach a))).trans hCore
  simpa only [hRow,_root_.sub_apply,clm_ite_zero_apply] using hLeft

lemma coordinateGradientAdjoint_angular (P : CoarseAngularFields) (k i j : I) :
    (coordinateGradientAdjoint P k).angular (i,j) =
      (if k=j then (coordinateGradientAdjoint P i).operator else 0)-
        (if k=i then (coordinateGradientAdjoint P j).operator else 0)+
          (P.angular (i,j)).comp (oneSphereCoordinateMulL k) := by
  change (coordinateTangentialAdjoint k).angular (i,j)+
    ((P.angular (i,j)).comp (oneSphereCoordinateMulL k)+P.operator.comp (coordinateAngularOneMul i j k)) = _
  rw [coordinateTangentialAdjoint_angular]
  have hIfAdd (P : Prop) [Decidable P] (A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
      (if P then A+B else 0)=(if P then A else 0)+(if P then B else 0) := by
    split_ifs <;> simp only [zero_add]
  simp only [coordinateGradientAdjoint,add,mulRight,coordinateScalarRotationData,
    coordinateAngularOneMul,ContinuousLinearMap.comp_sub,clm_comp_ite_zero,hIfAdd]
  abel
end CoarseAngularFields
end ShrinkingSpheres
