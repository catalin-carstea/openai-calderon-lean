import Proof.CoarseAngularProductPackets
import Proof.CoordinateRotationGenerator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

def coordinateRotationMultiplierSmoothData (k : I) : SmoothData :=
  ⟨(fun x : X => x k),(EuclideanSpace.proj k : X →L[ℝ] ℝ).contDiff⟩

def coordinateAngularOneMul (a b k : I) : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  (if k=b then oneSphereCoordinateMulL a else 0)-(if k=a then oneSphereCoordinateMulL b else 0)

def coordinateAngularCoarseMul (a b k : I) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  (if k=b then coarseSphereScalarMulL (sphereCoordinate a) else 0)-
    (if k=a then coarseSphereScalarMulL (sphereCoordinate b) else 0)

lemma smoothSphereValue_coordinate_rotation (a b k : I) :
    smoothSphereValue (smoothRotationData a b (coordinateRotationMultiplierSmoothData k)) =
      (if k=b then sphereCoordinate a else 0)-(if k=a then sphereCoordinate b else 0) := by
  apply ContinuousMap.ext
  intro w
  have hr : (((if k=b then sphereCoordinate a else 0)-(if k=a then sphereCoordinate b else 0)) : C(UnitSphere,ℝ)) w =
      (if k=b then w.val a else 0)-(if k=a then w.val b else 0) := by
    split_ifs <;> rfl
  rw [hr]
  change fderiv ℝ (fun x : X => x k) w.val (rotationVector a b w.val) =
    (if k=b then w.val a else 0)-(if k=a then w.val b else 0)
  have hd : HasFDerivAt (fun x : X => x k) (EuclideanSpace.proj k : X →L[ℝ] ℝ) w.val :=
    (EuclideanSpace.proj k : X →L[ℝ] ℝ).hasFDerivAt
  rw [hd.fderiv]
  change (rotationVector a b w.val) k = _
  simp [rotationVector,axis,PiLp.single_apply,Pi.single_apply,eq_comm]

lemma coordinateAngularCoarseMul_eq (a b k : I) :
    coarseSphereScalarMulL (smoothSphereValue (smoothRotationData a b (coordinateRotationMultiplierSmoothData k))) =
      coordinateAngularCoarseMul a b k := by
  change coarseScalarMultiplierMapL _ =
    (if k=b then coarseScalarMultiplierMapL (sphereCoordinate a) else 0)-
      (if k=a then coarseScalarMultiplierMapL (sphereCoordinate b) else 0)
  rw [smoothSphereValue_coordinate_rotation,map_sub]
  split_ifs <;> simp only [map_zero]

lemma coordinateAngularMultiplier_compatible (a b k : I) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (coordinateAngularOneMul a b k u) =
      coordinateAngularCoarseMul a b k (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  unfold coordinateAngularOneMul coordinateAngularCoarseMul
  split_ifs <;> simp only [_root_.sub_apply,_root_.zero_apply,map_sub,map_zero,
    oneSphereCoordinateMulL_coarse]

def coordinateScalarRotationData (k : I) : ScalarRotationMultiplierData where
  one := oneSphereCoordinateMulL k
  coarse := coarseSphereScalarMulL (sphereCoordinate k)
  angularOne ij := coordinateAngularOneMul ij.1 ij.2 k
  angularCoarse ij := coordinateAngularCoarseMul ij.1 ij.2 k
  compatible := oneSphereCoordinateMulL_coarse k
  symmetric := coarseSphereScalarMulL_symmetric _
  angularCompatible ij := coordinateAngularMultiplier_compatible ij.1 ij.2 k
  angularSymmetric := by
    intro ij u v
    rw [← coordinateAngularCoarseMul_eq]
    exact coarseSphereScalarMulL_symmetric _ _ _
  product := by
    intro ij u
    have hh := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u)
      (orderOneMultiplier_rotation_product (coordinateRotationMultiplierSmoothData k)
        (oneSphereCoordinateMulL k) (oneSphereCoordinateMulL_coarse k) ij.1 ij.2)
    have hc : smoothSphereValue (coordinateRotationMultiplierSmoothData k) = sphereCoordinate k := rfl
    simpa only [hc,coordinateAngularCoarseMul_eq,ContinuousLinearMap.comp_apply,_root_.add_apply] using hh

end ShrinkingSpheres
