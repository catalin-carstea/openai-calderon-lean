import Proof.WeakStrongPoissonCompatibility
import Proof.BoundaryNegativePairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeFullSharpHalfTrace
open OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace
open OAI.AnisotropicCalderon.NativeHalfTraceRightInverse
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Green's identity identifies the weak conormal endpoint with the ordinary
    H2 conormal trace whenever both arise from the same harmonic solution. -/
theorem nativeWeakConormal_eq_ordinary_trace {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (F : SmoothCoefficientMatrix 2)
    (hPoint : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = a x)
    (f : SphereSobolev (1/2:ℝ)) (U : BallSobolev 2)
    (hLift : nativeWeakHalfLift a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner f =
      TauCeti.Wkp.firstOrder 1 U)
    (hHarm : ordinaryPrincipalL fixedSobolevCalculus 0 F U = 0) :
    nativeWeakConormalEndpoint a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner f =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
          (ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace F U)) := by
  apply ext_inner_left ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ) z _ = sphereSobolevDualPairing (1/2:ℝ) z _
  rw [sphereSobolevDualPairing_nativeWeakConormalEndpoint]
  rw [hLift]
  have hEnergy := (energyFormH1_congr_coeff_on hPoint
    (TauCeti.Wkp.firstOrder 1 U) (fixedHarmonicH1LiftL z)).symm.trans
      (ordinaryPrincipalL_harmonic_full_test_energy fixedSobolevCalculus fixedUnitBallValueTrace
        F U hHarm (fixedHarmonicH1LiftL z))
  change sphereSurfaceMass⁻¹*TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ))
      (TauCeti.Wkp.firstOrder 1 U) (fixedHarmonicH1LiftL z) = _
  rw [hEnergy,← mul_assoc,inv_mul_cancel₀ sphereSurfaceMass_pos.ne',one_mul]
  apply Eq.symm
  apply boundary_negative_pairing z
    (nativeHalfCoefficientConormalTraceL sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace F U)
  · exact sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace F U
  · have ht := sphereSobolevInclusionL_nativeHalfTraceL sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace (fixedHarmonicH1LiftL z)
    have hr := nativeHalfTraceL_harmonicFirstOrderLiftCompletion sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace z
    exact (congrArg (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) hr).symm.trans ht

end ShrinkingSpheres
