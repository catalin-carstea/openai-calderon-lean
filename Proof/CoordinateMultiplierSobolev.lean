import Proof.FrameAdjointOperators
import Proof.Archive.SphereSobolevCoordinateInclusion
import Proof.Archive.NativeBoundaryCoefficientL2Decomposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def coordinateMultiplierSobolevL (s : ℝ) (i : I) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  sphereSobolevLinearCoordinateMulL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics s (axis i)

theorem coordinateMultiplierSobolevL_zero (i : I) :
    coordinateMultiplierSobolevL 0 i = coarseSphereScalarMulL (sphereCoordinate i) := by
  apply ContinuousLinearMap.ext
  intro u
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have h := sphereSobolevLinearCoordinateMulL_zeroEquiv sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics (axis i) (Z.symm u)
  have hLeft : sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (Z.symm u) = u :=
    Z.apply_symm_apply u
  rw [hLeft] at h
  change sphereSobolevLinearCoordinateMulL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics 0 (axis i) u =
    Z (sphereContinuousScalarMulL (sphereCoordinate i) (Z.symm u))
  simpa only [axis,sphereLinearCoordinateMulL_single,sphereCoordinateMulL_eq_scalarMulL,
    ] using h

theorem coordinateMultiplierSobolevL_coarse (i : I) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (coordinateMultiplierSobolevL 1 i u) =
      coarseSphereScalarMulL (sphereCoordinate i) (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  have h := sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics 1 0 (by norm_num) (axis i) u
  exact h.trans (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    T (sphereSobolevInclusionL 1 0 (by norm_num) u)) (coordinateMultiplierSobolevL_zero i))

theorem coordinate_normal_value (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    smoothSphereValue (coefficientSmoothData (vectorNormalJet (coordinateBoundaryCoefficients Q i))) =
      sphereCoordinate i := by
  ext w
  change coefficientValue 2 (vectorNormalJet (coordinateBoundaryCoefficients Q i)) w.val = _
  rw [coefficientValue_vectorNormalJet]
  change (∑ j : I,w.val j*(smoothSphereValue (coefficientSmoothData (coordinateBoundaryCoefficients Q i j)) w)) = _
  simp_rw [coordinateBoundaryCoefficients_sphere Q hQ]
  simp only [ContinuousMap.const_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

theorem oneBoundaryCoordinateMulL_eq (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    oneBoundaryCoefficientMulL (vectorNormalJet (coordinateBoundaryCoefficients Q i)) =
      coordinateMultiplierSobolevL 1 i := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  have hNormal := congrArg (fun q : C(UnitSphere,ℝ) =>
    coarseSphereScalarMulL q (sphereSobolevInclusionL 1 0 (by norm_num) u)) (coordinate_normal_value Q hQ i)
  exact (oneBoundaryCoefficientMulL_coarse (vectorNormalJet (coordinateBoundaryCoefficients Q i)) u).trans
    (hNormal.trans (coordinateMultiplierSobolevL_coarse i u).symm)

theorem norm_coordinateMultiplierSobolevL_one_le (i : I) : ‖coordinateMultiplierSobolevL 1 i‖ ≤ 6 := by
  have h := norm_sphereSobolevLinearCoordinateMulL_le sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics 1 (axis i)
  have hSum : (∑ j : I,|axis i j|) = 1 := by
    have hTerm (j : I) : |axis i j| = if j=i then 1 else 0 := by
      by_cases hj : j=i <;> simp [axis,hj]
    simp_rw [hTerm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hOne : radialDriftSobolevBound 1 = 1 := by norm_num [radialDriftSobolevBound]
  have hNeg : radialDriftSobolevBound (-1) = 2 := by norm_num [radialDriftSobolevBound]
  have hConst : (2*∑ j : I,|axis i j|)*(radialDriftSobolevBound 1+radialDriftSobolevBound (-1)) = 6 := by
    rw [hSum,hOne,hNeg]
    norm_num
  exact h.trans_eq hConst

theorem norm_coordinateMultiplierSobolevL_zero_le (i : I) : ‖coordinateMultiplierSobolevL 0 i‖ ≤ 1 := by
  rw [coordinateMultiplierSobolevL_zero]
  apply (norm_coarseSphereScalarMulL_le _).trans
  exact (ContinuousMap.norm_le _ zero_le_one).mpr (norm_sphereCoordinate_le i)

end ShrinkingSpheres
