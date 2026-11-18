import Proof.WeakConormalStrongTrace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments OAI.AnisotropicCalderon.NativeFullSharpHalfTrace
open OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace OAI.AnisotropicCalderon.NativeHalfTraceRightInverse
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence

/-- The first-variation forcing cancels in the two genuine strong Green identities. -/
theorem firstVariation_full_test_energy_Green (F0 F1 : SmoothCoefficientMatrix 2)
    (U0 U1 : BallSobolev 2)
    (hForce : fullCoefficientOperatorL fixedSobolevCalculus 0 F0 U1+
      fullCoefficientOperatorL fixedSobolevCalculus 0 F1 U0 = 0) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (coefficientMatrixField 2 F0) 0 0 (TauCeti.Wkp.firstOrder 1 U1) v+
      TauCeti.PDE.energyFormH1 (coefficientMatrixField 2 F1) 0 0 (TauCeti.Wkp.firstOrder 1 U0) v =
      sphereSurfaceMass*inner ℝ
        (ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace F0 U1+
          ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace F1 U0)
        (fixedUnitBallValueTrace.valueTraceL v) := by
  have hG0 := ordinaryPrincipalL_full_test_energy_Green fixedSobolevCalculus fixedUnitBallValueTrace F0 U1 v
  have hG1 := ordinaryPrincipalL_full_test_energy_Green fixedSobolevCalculus fixedUnitBallValueTrace F1 U0 v
  have hZero := congrArg (fun u : BallSobolev 0 => inner ℝ (TauCeti.Wkp.valueL 0 u) (TauCeti.W1p.value v)) hForce
  simp only [map_add,map_zero,inner_add_left,inner_zero_left] at hZero
  rw [hG0,hG1,inner_add_left]
  change inner ℝ (TauCeti.Wkp.value 0 (ordinaryPrincipalL fixedSobolevCalculus 0 F0 U1)) (TauCeti.W1p.value v)+
    inner ℝ (TauCeti.Wkp.value 0 (ordinaryPrincipalL fixedSobolevCalculus 0 F1 U0)) (TauCeti.W1p.value v) = 0 at hZero
  nlinarith only [hZero]


end ShrinkingSpheres
