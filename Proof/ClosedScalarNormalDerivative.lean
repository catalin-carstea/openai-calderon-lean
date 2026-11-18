import Proof.ClosedCoefficientDirectionalDerivative
import Proof.ClosedHalfScalarMultiplier
import Proof.CoordinateMultiplierSobolev
import Proof.HalfRadialMultiplierCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

def closedScalarNormalDerivativeHalfL : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  ∑ i : I,(ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) (SphereSobolev (1/2:ℝ))
    (SphereSobolev (1/2:ℝ)) (coordinateMultiplierSobolevL (1/2:ℝ) i)).comp
      (closedTwoJetHalfBoundaryScalarMultiplierL.comp (closedCoefficientDirectionalDerivativeL 2 (axis i)))

lemma closedScalarNormalDerivativeHalfL_on_smooth (Q : SmoothCoefficientJets 3) :
    closedScalarNormalDerivativeHalfL (smoothCoefficientClosureInclusionL 3 Q)=
      nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace Q := by
  have hDer (i : I) : smoothCoefficientDirectionalDerivative 2 (axis i) Q=smoothMultiplierDerivativeJets Q i := by
    apply smoothCoefficientJets_ext_of_value
    rw [coefficientValue_smoothCoefficientDirectionalDerivative,smoothMultiplierDerivativeJets,coefficientValue_compactCoefficient]
    rfl
  simp only [closedScalarNormalDerivativeHalfL,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    closedCoefficientDirectionalDerivativeL_on_smooth,closedTwoJetHalfBoundaryScalarMultiplierL_on_smooth,hDer]
  rfl
end ShrinkingSpheres
