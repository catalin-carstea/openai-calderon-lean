import Proof.NativeBoundaryCalculus
import Proof.Archive.NativeH2AffineStrongKernel
import Proof.Archive.NativeHarmonicLiftOrderCoherence
import Proof.Archive.CollaboratorUnitBallValueTraceKernelOct17
import Proof.Archive.NativeCoefficientWeakConormalEndpoint
import Proof.Archive.NativeHalfCoefficientConormalTrace
import Proof.Archive.NativeCoefficientBoundaryMultiplier
import Proof.Archive.NativeH2ConormalRadialConversion
import Proof.Archive.SphereSobolevBalancedDualInterpolationLinear

noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- The fixed value trace has exactly the zero Dirichlet Sobolev kernel. -/
theorem fixedUnitBallValueTrace_kernel : UnitBallValueTraceKernel fixedUnitBallValueTrace :=
  unitBallValueTraceKernel fixedUnitBallValueTrace

/-- Canonical half-order value trace and its Euclidean Poisson right inverse. -/
def fixedHalfValueTraceL : BallH1 →L[ℝ] SphereSobolev (1/2:ℝ) :=
  OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace

def fixedHarmonicH1LiftL : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion sphereFischerInner

theorem fixedHalfValueTrace_right_inverse :
    fixedHalfValueTraceL.comp fixedHarmonicH1LiftL = ContinuousLinearMap.id ℝ _ :=
  OAI.AnisotropicCalderon.NativeHalfTraceRightInverse.nativeHalfTraceL_comp_harmonicFirstOrderLiftCompletion
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace

end ShrinkingSpheres
