import Proof.StrongPoissonTaylor
import Proof.PolynomialAffineCoefficient
import Proof.PolynomialDriftDirichlet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory MvPolynomial
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SpectralCoreRegularity OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open OAI.AnisotropicCalderon.GreenRadialTrace

lemma fixedHarmonicLift_single (k : ℕ) (a : harmonicSphereSubspace k) :
    fixedHarmonicLiftL (sphereSobolevSingleL (3/2:ℝ) k a) =
      polynomialBallSobolev 2 (harmonicPolynomialRepresentativeL sphereFischerInner k a) := by
  let b : HarmonicFiniteCoefficients := DirectSum.lof ℝ ℕ (fun j => ↥(harmonicSphereSubspace j)) k a
  have h := harmonicLiftCompletion_finite sphereFischerInner orthogonalSphereHarmonics b
  simpa only [b,harmonicBoundaryFiniteL,harmonicNativeFiniteL,DirectSum.toModule_lof,
    LinearMap.comp_apply,ContinuousLinearMap.coe_coe,fixedHarmonicLiftL,polynomialBallSobolevLinearMap,
    LinearMap.coe_mk,AddHom.coe_mk] using h

/-- The actual canonical first Poisson variation is the explicit zero-boundary
    polynomial drift variation whenever the Euclidean lift is polynomial. -/
theorem strongFirstPoissonVariation_polynomial (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : c ≠ 0) (L : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ (ballOpens : Set X),∀ i j,coefficientValue 2 (F1 i j) x = L x*(1:Mat) i j)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    {k : ℕ} (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0)
    (f : SphereSobolev (3/2:ℝ)) (hLift : fixedHarmonicLiftL f = polynomialBallSobolev 2 p) :
    strongFirstPoissonVariationL F0 F1 c f =
      c⁻¹ • polynomialBallSobolev 2 (driftFirstVariation k (fun i => L (axis i)) p) := by
  change -(fixedStrongH2InclusionL
    ((strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse
      (fullCoefficientOperatorL fixedSobolevCalculus 0 F1 (fixedHarmonicLiftL f)))) = _
  rw [hLift,fullCoefficientOperator_affine_harmonic_polynomial fixedSobolevCalculus F1 L hF1 p hΔ,
    map_neg,flat_inverse_polynomial_drift F0 hF0 c hc hInv p hp hΔ (fun i => L (axis i)),map_neg,neg_neg,map_smul]
  rfl

/-- On every positive harmonic degree the coarse first radial variation is
    exactly the supplied bounded radial drift operator, with its center scale. -/
theorem firstRadialVariation_polynomial (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : c ≠ 0) (L : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ (ballOpens : Set X),∀ i j,coefficientValue 2 (F1 i j) x = L x*(1:Mat) i j)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (m : ℕ) (p : harmonicHomogeneous (m+1)) (f : SphereSobolev (3/2:ℝ))
    (hLift : fixedHarmonicLiftL f = polynomialBallSobolev 2 p) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (highFirstRadialVariationL F0 F1 c f) =
      c⁻¹ • sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialDriftTraceL sphereFischerInner
          orthogonalSphereHarmonics denseSphereHarmonics
          (WithLp.toLp 2 (fun i => L (axis i))) (polynomialSphereL2 p)) := by
  have hP := strongFirstPoissonVariation_polynomial F0 F1 c hc L hF0 hF1 hInv p p.property.1 p.property.2 f hLift
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (fixedHalfOutwardTraceL (strongFirstPoissonVariationL F0 F1 c f)) = _
  rw [hP,map_smul,map_smul]
  have hTrace := OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.sphereSobolevInclusionL_nativeHalfOutwardTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace
    (polynomialBallSobolev 2 (driftFirstVariation (m+1) (fun i => L (axis i)) p))
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (fixedHalfOutwardTraceL (polynomialBallSobolev 2 (driftFirstVariation (m+1) (fun i => L (axis i)) p))) = _ at hTrace
  rw [hTrace]
  rw [outwardRadialTraceL_driftFirstVariation fixedSobolevCalculus fixedUnitBallValueTrace (by omega),
    OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialDriftTraceL_polynomial sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics]
  rfl

end ShrinkingSpheres
