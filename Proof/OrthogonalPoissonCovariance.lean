import Proof.WeakStrongPoissonCompatibility
import Proof.NativeWeakInverseBound
import Proof.RadialEndpointCompatibility
import Proof.Archive.NativeWeakHalfLiftOrthogonalCovariance
import Proof.Archive.NativeH2OutwardTraceOrthogonalCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion
open OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeWeakHalfLift functionalInverse nativeZeroFunctionalInverse
  OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion

/-- The genuine strong Poisson lift commutes with orthogonal coordinate
    changes, through the same actual weak solution. -/
theorem strongPoissonL_orthogonal_covariance
    (e : X ≃ₗᵢ[ℝ] X) (a : X → Mat) (ha : Continuous a)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) (0:X) (0:ℝ)) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hrot : MemLp (fun z => TauCeti.PDE.energyIntegrand (orthogonalPrincipalCoefficient e a z) (0:X) (0:ℝ)) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff))
    (hcr : IsCoercive (TauCeti.PDE.energyFormH1L0 hrot))
    (F G : SmoothCoefficientMatrix 2)
    (hF : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = a z)
    (hG : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 G z = orthogonalPrincipalCoefficient e a z)
    (hIF : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hIG : (strongDirichletOperator fixedSobolevCalculus 0 G).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    strongPoissonL G (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f) =
      nativeH2OrthogonalPullback fixedSobolevCalculus e (strongPoissonL F f) := by
  have hB : orthogonalDriftCoefficient e (fun _ => (0:X)) = (fun _ => (0:X)) := by
    funext z
    exact e.symm.map_zero
  have hrot' : MemLp (fun z => TauCeti.PDE.energyIntegrand (orthogonalPrincipalCoefficient e a z)
      (orthogonalDriftCoefficient e (fun _ => (0:X)) z) (((fun _ => (0:ℝ)) ∘ e) z)) ⊤
        ((volume:Measure X).restrict ballOpens) := by
    simpa only [hB,Function.comp_def] using hrot
  have hInv := isInvertible_of_bilinear_coercive _ hc
  have hInvRot : (TauCeti.PDE.energyFormH1L0 hrot').IsInvertible := by
    simpa only [hB,Function.comp_def] using isInvertible_of_bilinear_coercive _ hcr
  have hCov := nativeWeakHalfLift_orthogonal_covariance e a (fun _ => (0:X)) (fun _ => (0:ℝ))
    ha continuous_const continuous_const hcoeff hrot' sphereFischerInner orthogonalSphereHarmonics
      hInv hInvRot (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
  simp only [hB,Function.comp_def] at hCov
  have hOld := nativeWeakHalfLift_eq_strongPoisson hcoeff hc F hF hIF f
  have hNew := nativeWeakHalfLift_eq_strongPoisson hrot hcr G hG hIG
    (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f)
  have hInput := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f)
    (sphereSobolevInclusionL_orthogonalPullback (3/2:ℝ) (1/2:ℝ) (by norm_num) e)
  apply nativeH2_firstOrder_injective
  rw [firstOrder_nativeH2OrthogonalPullback]
  exact hNew.symm.trans ((congrArg (nativeWeakHalfLift (orthogonalPrincipalCoefficient e a)
    (fun _ => (0:X)) (fun _ => (0:ℝ)) hrot sphereFischerInner) hInput).trans
      (hCov.symm.trans (congrArg (nativeH1OrthogonalPullback e) hOld)))

/-- The actual high radial response transforms under the same orthogonal
    action on boundary data and output. -/
theorem highRadialResponse_orthogonal_covariance
    (e : X ≃ₗᵢ[ℝ] X) (F G : SmoothCoefficientMatrix 2)
    (hPoisson : ∀ f : SphereSobolev (3/2:ℝ),
      strongPoissonL G (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f) =
        nativeH2OrthogonalPullback fixedSobolevCalculus e (strongPoissonL F f))
    (f : SphereSobolev (3/2:ℝ)) :
    fixedHalfOutwardTraceL (strongPoissonL G (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f)) =
      sphereSobolevOrthogonalPullbackL (1/2:ℝ) e (fixedHalfOutwardTraceL (strongPoissonL F f)) := by
  have hTrace := nativeHalfOutwardTraceL_nativeH2OrthogonalPullback sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace e (strongPoissonL F f)
  exact (congrArg fixedHalfOutwardTraceL (hPoisson f)).trans hTrace

lemma fixedHarmonicLiftL_orthogonal_covariance (e : X ≃ₗᵢ[ℝ] X) (f : SphereSobolev (3/2:ℝ)) :
    fixedHarmonicLiftL (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f) =
      nativeH2OrthogonalPullback fixedSobolevCalculus e (fixedHarmonicLiftL f) := by
  have hOld := firstOrder_harmonicLiftCompletion sphereFischerInner orthogonalSphereHarmonics f
  have hNew := firstOrder_harmonicLiftCompletion sphereFischerInner orthogonalSphereHarmonics
    (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f)
  have hInput := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f)
    (sphereSobolevInclusionL_orthogonalPullback (3/2:ℝ) (1/2:ℝ) (by norm_num) e)
  have hCov := OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion_orthogonalPullback
    sphereFischerInner orthogonalSphereHarmonics e
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
  apply nativeH2_firstOrder_injective
  rw [firstOrder_nativeH2OrthogonalPullback]
  exact hNew.trans ((congrArg fixedHarmonicH1LiftL hInput).trans
    (hCov.symm.trans (congrArg (nativeH1OrthogonalPullback e) hOld.symm)))

theorem actualHighRadialErrorL_orthogonal_covariance
    (e : X ≃ₗᵢ[ℝ] X) (F G : SmoothCoefficientMatrix 2)
    (hPoisson : ∀ f : SphereSobolev (3/2:ℝ),
      strongPoissonL G (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f) =
        nativeH2OrthogonalPullback fixedSobolevCalculus e (strongPoissonL F f)) :
    (actualHighRadialErrorL G).comp (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e) =
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e).comp (actualHighRadialErrorL F) := by
  apply ContinuousLinearMap.ext
  intro f
  have hStrong := highRadialResponse_orthogonal_covariance e F G hPoisson f
  have hFlatTrace := nativeHalfOutwardTraceL_nativeH2OrthogonalPullback sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace e (fixedHarmonicLiftL f)
  have hFlat : fixedHalfOutwardTraceL (fixedHarmonicLiftL (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f)) =
      sphereSobolevOrthogonalPullbackL (1/2:ℝ) e (fixedHalfOutwardTraceL (fixedHarmonicLiftL f)) :=
    (congrArg fixedHalfOutwardTraceL (fixedHarmonicLiftL_orthogonal_covariance e f)).trans hFlatTrace
  change fixedHalfOutwardTraceL (strongPoissonL G (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f))-
    fixedHalfOutwardTraceL (fixedHarmonicLiftL (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f)) =
      sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
        (fixedHalfOutwardTraceL (strongPoissonL F f)-fixedHalfOutwardTraceL (fixedHarmonicLiftL f))
  rw [hStrong,hFlat,map_sub]

end ShrinkingSpheres
