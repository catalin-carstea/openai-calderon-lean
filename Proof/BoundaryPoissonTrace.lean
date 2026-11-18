import Proof.StrongPoissonIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility

/-- The canonical L2 realization of H3/2 boundary data. -/
def fixedBoundaryValueL : SphereSobolev (3/2:ℝ) →L[ℝ] SphereL2 :=
  ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num))

/-- The completed Euclidean lift has exactly its prescribed native L2 trace. -/
theorem fixedBoundaryValueL_harmonicLift (f : SphereSobolev (3/2:ℝ)) :
    fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)) =
      fixedBoundaryValueL f := by
  apply (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).injective
  change sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (strongValueTraceL fixedUnitBallValueTrace 0 (fixedHarmonicLiftL f)) =
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics)
      ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) f))
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion]
  exact sphereSobolevCoefficientL_zeroEquiv_strongValueTraceL_harmonicLiftCompletion
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace k f

/-- The corrected actual Poisson lift retains the same prescribed trace. -/
theorem fixedBoundaryValueL_strongPoisson (F : SmoothCoefficientMatrix 2)
    (f : SphereSobolev (3/2:ℝ)) :
    fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) =
      fixedBoundaryValueL f :=
  (strongPoissonL_valueTrace F f).trans (fixedBoundaryValueL_harmonicLift f)

end ShrinkingSpheres
