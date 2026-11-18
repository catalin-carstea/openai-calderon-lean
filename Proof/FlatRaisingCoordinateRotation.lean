import Proof.FlatRaisingSobolev
import Proof.CoordinateScalarRotationPacket
import Proof.OrderOneCoefficientAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

lemma coordinateBoundaryTangentialAdjoint_eq (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) :
    adjointBoundaryTangentialL (coordinateBoundaryCoefficients Q i)=
      -(∑ k : I,(sphereSobolevRotationL 1 k i).comp (coordinateMultiplierSobolevL 1 k)) := by
  have hF (j : I) : oneBoundaryCoefficientMulL (coordinateBoundaryCoefficients Q i j)=
      (if j=i then (1:ℝ) else 0) • ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
    apply oneBoundaryCoefficientMulL_const_sphere
    intro w
    change smoothSphereValue (coefficientSmoothData (coordinateBoundaryCoefficients Q i j)) w=_
    rw [coordinateBoundaryCoefficients_sphere Q hQ i j]
    rfl
  have hRow (j : I) : (∑ k : I,-(sphereSobolevRotationL 1 k j).comp
      ((oneSphereCoordinateMulL k).comp (oneBoundaryCoefficientMulL (coordinateBoundaryCoefficients Q i j))))=
      if j=i then -(∑ k : I,(sphereSobolevRotationL 1 k i).comp (coordinateMultiplierSobolevL 1 k)) else 0 := by
    by_cases hj : j=i
    · subst j
      simp only [hF,ite_true,one_smul,ContinuousLinearMap.comp_id,Finset.sum_neg_distrib]
      rfl
    · simp only [hF,ite_eq_right hj,zero_smul,ContinuousLinearMap.comp_zero,neg_zero,Finset.sum_const_zero]
  simp only [adjointBoundaryTangentialL,hRow,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Reorder the exact flat raising operator so rotations and degree act
    before the coordinate multipliers. The remaining term is order zero. -/
lemma flatRaising_coordinate_rotation (i : I) (u : SphereSobolev 1) :
    flatRaisingSobolevL 1 i u=
      -(∑ k : I,coordinateMultiplierSobolevL 0 k (sphereSobolevRotationL 1 k i u))+
      coordinateMultiplierSobolevL 0 i (sphereSobolevDegreeL u)+
      ((2:ℝ) • coordinateMultiplierSobolevL 0 i+coordinateDegreeCommutatorL i)
        (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  have hFlat : flatRaisingSobolevL 1 i u=
      -(∑ k : I,sphereSobolevRotationL 1 k i (coordinateMultiplierSobolevL 1 k u))+
      sphereSobolevDegreeL (coordinateMultiplierSobolevL 1 i u) := by
    rw [flatRaisingSobolevL_one Q hQ,boundaryGradientAdjointL,
      coordinateBoundaryTangentialAdjoint_eq Q hQ i,oneBoundaryCoordinateMulL_eq Q hQ i]
    simp only [_root_.add_apply,_root_.neg_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply]
  let v := sphereSobolevInclusionL 1 0 (by norm_num) u
  have hOne (k : I) : oneSphereCoordinateMulL k=coordinateMultiplierSobolevL 1 k := rfl
  have hRot (k : I) : sphereSobolevRotationL 1 k i (coordinateMultiplierSobolevL 1 k u)=
      (if k=i then coordinateMultiplierSobolevL 0 k v else 0)-coordinateMultiplierSobolevL 0 i v+
      coordinateMultiplierSobolevL 0 k (sphereSobolevRotationL 1 k i u) := by
    have h := (coordinateScalarRotationData k).product (k,i) u
    by_cases hki : k=i
    · simpa [coordinateScalarRotationData,coordinateAngularCoarseMul,hki,hOne,
        ← coordinateMultiplierSobolevL_zero,v] using h
    · simpa [coordinateScalarRotationData,coordinateAngularCoarseMul,hki,hOne,
        ← coordinateMultiplierSobolevL_zero,v] using h
  have hSum : (∑ k : I,sphereSobolevRotationL 1 k i (coordinateMultiplierSobolevL 1 k u))=
      -(2:ℝ) • coordinateMultiplierSobolevL 0 i v+
      ∑ k : I,coordinateMultiplierSobolevL 0 k (sphereSobolevRotationL 1 k i u) := by
    simp only [hRot,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [Fin.sum_univ_three]
    module
  have hDegree := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
    (degree_coordinateMultiplier_commutator i)
  change sphereSobolevDegreeL (coordinateMultiplierSobolevL 1 i u)-
    coordinateMultiplierSobolevL 0 i (sphereSobolevDegreeL u)=coordinateDegreeCommutatorL i v at hDegree
  rw [hFlat,hSum,sub_eq_iff_eq_add.mp hDegree]
  simp only [_root_.add_apply,_root_.smul_apply,v]
  module
end ShrinkingSpheres
