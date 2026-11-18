import Proof.Archive.CollaboratorFixedSobolevCalculusOct17
import Proof.Archive.ActualNativeValueTraceExistence
import Proof.Archive.NativeFullHalfRadialTrace
import Proof.Archive.NativeHalfTraceRightInverse
import Proof.Archive.NativeHarmonicLiftExtension
import Proof.Archive.LiteratureSphereFischerInner
import Proof.Archive.LiteratureOrthogonalSphereHarmonics
import Proof.Archive.LiteratureDenseSphereHarmonics

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- A fixed native trace supplied by the selected constructive trace proof. -/
def fixedUnitBallValueTrace : UnitBallValueTrace :=
  Classical.choice OAI.AnisotropicCalderon.MixedKernelConstructionTask.nonempty_unitBallValueTrace

/-- The actual canonical radial trace on H2, with its half-order target. -/
def fixedHalfOutwardTraceL : BallSobolev 2 →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.nativeHalfOutwardTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    fixedSobolevCalculus fixedUnitBallValueTrace

/-- The Euclidean Poisson extension, completed in H2 from finite harmonics. -/
def fixedHarmonicLiftL : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2 :=
  OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion.harmonicLiftCompletion sphereFischerInner

end ShrinkingSpheres
