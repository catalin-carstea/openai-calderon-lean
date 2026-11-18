import Proof.OrderOneBoundaryCoefficient
import Proof.Archive.NativeH2SmoothMultiplierOutwardTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier

lemma halfBoundaryCoefficientMul_coarse (Q : SmoothCoefficientJets 3) (f : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
        fixedUnitBallValueTrace (smoothMultiplierLowerJets Q) f) =
    coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) f) :=
  sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace Q (smoothMultiplierLowerJets Q)
    (coefficientValue_smoothMultiplierLowerJets Q).symm f

/-- The same actual smooth multiplication commutes with high-to-H1
restriction, including the native choice of its third-jet representative. -/
theorem oneBoundaryCoefficientMulL_third_high (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2:ℝ)) :
    oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q)
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
    sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
      (nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
        fixedUnitBallValueTrace Q f) := by
  let M0 := coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
  let M3 := nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  let I1 := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
  let J0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let I0 := sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
  have hTrans (v : SphereSobolev (3/2:ℝ)) : J0 (I1 v) = I0 v :=
    congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T v)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 0 (by norm_num) (by norm_num))
  have hm : coefficientSmoothData (smoothMultiplierLowerJets Q) = nativeH2CoefficientSmoothData Q :=
    Subtype.ext (coefficientValue_smoothMultiplierLowerJets Q)
  have hOne := oneBoundaryCoefficientMulL_coarse (smoothMultiplierLowerJets Q) (I1 f)
  rw [hm] at hOne
  have hLeft : J0 (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q) (I1 f)) = M0 (I0 f) :=
    hOne.trans (congrArg M0 (hTrans f))
  have hRight : J0 (I1 (M3 f)) = M0 (I0 f) := (hTrans (M3 f)).trans
    (sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace Q f)
  exact sphereSobolevInclusionL_injective 1 0 (by norm_num) (hLeft.trans hRight.symm)

end ShrinkingSpheres
