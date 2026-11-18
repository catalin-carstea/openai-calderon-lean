import Proof.CoarseScalarInverse
import Proof.RadialConversionCalculus
import Proof.Archive.NativeNegativeHalfMultiplierL2Inclusion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeNegativeHalfSmoothMultiplier

theorem negativeBoundaryCoefficientMulL_coarse (F : SmoothCoefficientJets 2) (u : SphereSobolev 0) :
    negativeBoundaryCoefficientMulL F (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData F)) u) := by
  obtain ⟨M,hM,hValue,hGradient⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  have hEq := nativeNegativeHalfCoefficientMulL_eq_smoothMulL fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace F hM hValue hGradient
  have h := congrArg (fun A : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    A (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u)) hEq
  exact h.trans (nativeNegativeHalfSmoothMulL_zero_inclusion sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace (coefficientSmoothData F) hM hValue hGradient u)

theorem negativeBoundaryCoefficientMulL_one_compatible (F : SmoothCoefficientJets 2) :
    (negativeBoundaryCoefficientMulL F).comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) =
      (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)).comp (oneBoundaryCoefficientMulL F) := by
  apply ContinuousLinearMap.ext
  intro u
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let I := sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)
  have hTrans := sphereSobolevInclusionL_trans 1 0 (-(1/2:ℝ)) (by norm_num) (by norm_num)
  have hIn := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u) hTrans
  have hOut := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    T (oneBoundaryCoefficientMulL F u)) hTrans
  exact (congrArg (negativeBoundaryCoefficientMulL F) hIn.symm).trans
    ((negativeBoundaryCoefficientMulL_coarse F (I0 u)).trans
      ((congrArg J (oneBoundaryCoefficientMulL_coarse F u)).symm.trans hOut))

end ShrinkingSpheres
