import Proof.FlatDegreeCompatibility
import Proof.BoundaryGradientRealization
import Proof.ConstantBoundaryCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory MvPolynomial
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion

theorem fixedHalfValueTrace_harmonicLift (f : SphereSobolev (3/2:ℝ)) :
    fixedHalfValueTraceL (TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)) =
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f := by
  have hOrder := OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence.firstOrder_harmonicLiftCompletion
    sphereFischerInner orthogonalSphereHarmonics f
  have hRight := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) =>
    T (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) fixedHalfValueTrace_right_inverse
  exact (congrArg fixedHalfValueTraceL hOrder).trans hRight

/-- The degree operator is the genuine outward radial trace of the completed
    Euclidean harmonic extension, on their common high boundary domain. -/
theorem sphereSobolevDegreeL_harmonicLift (f : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDegreeL (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (fixedHarmonicLiftL f)) := by
  let u := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  have hInput : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u =
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f :=
    congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
  have hLow := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u)
    fixedLowRadialL_degree_compatible
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  exact hLow.symm.trans ((congrArg fixedLowRadialL hInput).trans (fixedLowRadialL_high f))

/-- Constant ambient coordinate vector coefficients, represented by a common
    compact cutoff which is one near the closed unit ball. -/
def coordinateBoundaryCoefficients (Q : SmoothCoefficientJets 2) (i j : I) : SmoothCoefficientJets 2 :=
  constantBoundaryCoefficient Q (if j=i then 1 else 0)

theorem coordinateBoundaryCoefficients_sphere (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i j : I) :
    smoothSphereValue (coefficientSmoothData (coordinateBoundaryCoefficients Q i j)) =
      ContinuousMap.const UnitSphere (if j=i then 1 else 0) := by
  ext w
  have hw : w.val ∈ Metric.closedBall (0:X) 1 := by
    have hn : ‖w.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using w.property
    simpa [Metric.mem_closedBall,dist_zero_right,hn]
  exact (constantBoundaryCoefficient_germ Q hQ _ w.val hw).eq_of_nhds

lemma sphereContinuousScalarMulL_const_apply (c : ℝ) (u : SphereL2) :
    sphereContinuousScalarMulL (ContinuousMap.const UnitSphere c) u = c • u := by
  apply Lp.ext
  filter_upwards [sphereContinuousScalarMul_value_ae (ContinuousMap.const UnitSphere c) u,
    Lp.coeFn_smul c u] with w hw hu
  exact hw.trans hu.symm

/-- The flat boundary-gradient construction acts on the actual harmonic lift
    by its ordinary ambient coordinate derivative. -/
theorem coordinateBoundaryGradientL_high (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (f : SphereSobolev (3/2:ℝ)) :
    boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace i (fixedHarmonicLiftL f)) := by
  let u := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f
  have hInput : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u =
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f :=
    congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
  have hValue := fixedHalfValueTrace_harmonicLift f
  have hMain := boundaryGradientL_nativeH2 (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL
    (fixedHarmonicLiftL f) u (hValue.trans hInput.symm) (sphereSobolevDegreeL_harmonicLift f)
  have hSum : (∑ j : I,sphereContinuousScalarMulL
      (smoothSphereValue (coefficientSmoothData (coordinateBoundaryCoefficients Q i j)))
        (strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j (fixedHarmonicLiftL f))) =
      strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace i (fixedHarmonicLiftL f) := by
    simp only [coordinateBoundaryCoefficients_sphere Q hQ,sphereContinuousScalarMulL_const_apply]
    simp
  exact hMain.trans (congrArg (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics) hSum)

theorem strongCoordinateTraceL_polynomial (i : I) (p : MvPolynomial I ℝ) :
    strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace i (polynomialBallSobolev 2 p) =
      polynomialSphereL2 (pderiv i p) := by
  rw [polynomialBallSobolev,strongCoordinateTraceL_smooth,
    smoothCoordinateDerivative_smoothPolynomialData]
  rfl

theorem coordinateBoundaryGradientL_single (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (k : ℕ) (a : harmonicSphereSubspace k) :
    boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL
      (sphereSobolevSingleL 1 k a) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (polynomialSphereL2 (pderiv i (harmonicPolynomialRepresentativeL sphereFischerInner k a))) := by
  have h := coordinateBoundaryGradientL_high Q hQ i (sphereSobolevSingleL (3/2:ℝ) k a)
  rw [sphereSobolevInclusionL_single,fixedHarmonicLift_single,strongCoordinateTraceL_polynomial] at h
  exact h

end ShrinkingSpheres
