import Proof.CoordinateMultiplierSobolev
import Proof.OrderOneCoefficientAlgebra
import Proof.Archive.NativeH2SmoothMultiplierDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

def coordinateScalarSmoothJet (Q : SmoothCoefficientJets 2) (j : I) : SmoothCoefficientJets 3 :=
  coefficientThirdJet (vectorNormalJet (coordinateBoundaryCoefficients Q j))

lemma coordinateScalarSmoothJet_value (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (j : I) (w : UnitSphere) : coefficientValue 3 (coordinateScalarSmoothJet Q j) w.val = w.val j := by
  rw [coordinateScalarSmoothJet,coefficientValue_coefficientThirdJet]
  exact congrArg (fun F : C(UnitSphere,ℝ) => F w) (coordinate_normal_value Q hQ j)

lemma coordinateScalarSmoothJet_one_multiplier (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (j : I) (c : ℝ) :
    oneBoundaryCoefficientMulL (smoothMultiplierLowerJets (c • coordinateScalarSmoothJet Q j)) =
      c • coordinateMultiplierSobolevL 1 j := by
  have hCong := oneBoundaryCoefficientMulL_congr_sphere
    (smoothMultiplierLowerJets (c • coordinateScalarSmoothJet Q j))
    (c • vectorNormalJet (coordinateBoundaryCoefficients Q j)) (by
      intro w
      rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_smul,coefficientValue_smul]
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [coordinateScalarSmoothJet,coefficientValue_coefficientThirdJet])
  rw [hCong,oneBoundaryCoefficientMulL_smul,oneBoundaryCoordinateMulL_eq Q hQ j]

lemma coordinateScalarSmoothJet_coarse_multiplier (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (j : I) (c : ℝ) :
    coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData (c • coordinateScalarSmoothJet Q j))) =
      c • coordinateMultiplierSobolevL 0 j := by
  have hValue : smoothSphereValue (nativeH2CoefficientSmoothData (c • coordinateScalarSmoothJet Q j)) =
      c • sphereCoordinate j := by
    ext w
    change coefficientValue 3 (c • coordinateScalarSmoothJet Q j) w.val = c*w.val j
    rw [coefficientValue_smul]
    simp only [Pi.smul_apply,smul_eq_mul,coordinateScalarSmoothJet_value Q hQ]
  rw [hValue,coarseSphereScalarMulL_smul,coordinateMultiplierSobolevL_zero]
end ShrinkingSpheres
