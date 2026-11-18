import Proof.FlatHarmonicBoundaryGradient
import Proof.Archive.AngularShiftGraph
import Proof.Archive.NativeHarmonicFiniteBulkSquares

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory MvPolynomial
open scoped ENNReal Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open OAI.AnisotropicCalderon.HarmonicDerivativeOperator OAI.AnisotropicCalderon.AngularShiftGraph
open OAI.AnisotropicCalderon.SphereHilbertDecomposition OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SpectralCoreRegularity

theorem polynomialRepresentative_derivative (k : ℕ) (i : I) (a : harmonicSphereSubspace (k+1)) :
    polynomialSphereL2 (pderiv i (harmonicPolynomialRepresentativeL sphereFischerInner (k+1) a)) =
      (harmonicDerivative sphereFischerInner k i a : SphereL2) := by
  let p : harmonicHomogeneous (k+1) :=
    ⟨harmonicPolynomialRepresentativeL sphereFischerInner (k+1) a,
      harmonicPolynomialRepresentative_mem sphereFischerInner (k+1) a⟩
  have hInput : OAI.AnisotropicCalderon.SmoothSphereRotationProjection.harmonicPolynomialSphereMap (k+1) p = a :=
    Subtype.ext (polynomialSphereL2_harmonicPolynomialRepresentative sphereFischerInner (k+1) a)
  have h := congrArg Subtype.val (harmonicDerivative_apply_image sphereFischerInner k i p)
  rw [hInput] at h
  exact h.symm

theorem polynomialRepresentative_derivative_zero (i : I) (a : harmonicSphereSubspace 0) :
    polynomialSphereL2 (pderiv i (harmonicPolynomialRepresentativeL sphereFischerInner 0 a)) = 0 := by
  rw [OAI.AnisotropicCalderon.NativeHarmonicFiniteBulkSquares.pderiv_eq_zero_of_homogeneous_zero _
    (harmonicPolynomialRepresentative_mem sphereFischerInner 0 a).1 i,map_zero]

theorem coordinateBoundaryGradientL_single_succ (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (k : ℕ) (a : harmonicSphereSubspace (k+1)) :
    boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL
      (sphereSobolevSingleL 1 (k+1) a) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (harmonicDerivative sphereFischerInner k i a : SphereL2) :=
  (coordinateBoundaryGradientL_single Q hQ i (k+1) a).trans
    (congrArg (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics)
      (polynomialRepresentative_derivative k i a))

theorem coordinateBoundaryGradientL_single_zero (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (a : harmonicSphereSubspace 0) :
    boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL
      (sphereSobolevSingleL 1 0 a) = 0 := by
  have h := coordinateBoundaryGradientL_single Q hQ i 0 a
  rw [polynomialRepresentative_derivative_zero,map_zero] at h
  exact h

/-- On the complete H1 domain the flat boundary gradient is the supplied
    closed harmonic lowering operator, not merely a formally similar map. -/
theorem coordinateBoundaryGradientL_graph (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u : SphereSobolev 1) :
    ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u)) ∈
      sphereDerivativeGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let G := sphereDerivativeGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
  let T : SphereSobolev 1 →L[ℝ] SphereL2 × SphereL2 :=
    (Z.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (sphereSobolevInclusionL 1 0 (by norm_num))).prod
      (Z.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL))
  have hSingle (k : ℕ) (a : harmonicSphereSubspace k) : T (sphereSobolevSingleL 1 k a) ∈ G := by
    change (Z.symm (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevSingleL 1 k a)),
      Z.symm (boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL
        (sphereSobolevSingleL 1 k a))) ∈ G
    rw [sphereSobolevInclusionL_single,← zeroEquiv_harmonic_subtype,Z.symm_apply_apply]
    cases k with
    | zero =>
      rw [coordinateBoundaryGradientL_single_zero Q hQ,map_zero]
      exact sphereDerivativeGraph_constant sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i a
    | succ k =>
      rw [coordinateBoundaryGradientL_single_succ Q hQ,Z.symm_apply_apply]
      exact sphereDerivativeGraph_single sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i k a
  change T u ∈ G
  apply (isClosed_sphereDerivativeGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i).mem_of_tendsto
    (T.continuous.continuousAt.tendsto.comp (tendsto_sphereSobolevPartialSum 1 u))
  apply Eventually.of_forall
  intro n
  change T (sphereSobolevPartialSum 1 n u) ∈ G
  rw [sphereSobolevPartialSum,map_sum]
  exact G.sum_mem (fun k hk => hSingle k (sphereSobolevCoefficientL 1 k u))

theorem coordinateBoundaryGradientAdjointL_single_test (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u : SphereSobolev 1) (k : ℕ) (a : harmonicSphereSubspace k) :
    ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u),(a:SphereL2)⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) u),
        polynomialSphereL2 (pderiv i (harmonicPolynomialRepresentativeL sphereFischerInner k a))⟫_ℝ := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let U := Z.symm (sphereSobolevInclusionL 1 0 (by norm_num) u)
  let R := Z.symm (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u)
  have h := boundaryGradientL_adjoint (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL sphereSobolevDegreeL
    sphereSobolevDegreeL_symmetric (sphereSobolevSingleL 1 k a) u
  rw [coordinateBoundaryGradientL_single Q hQ,sphereSobolevInclusionL_single,← zeroEquiv_harmonic_subtype] at h
  have hU : Z U = sphereSobolevInclusionL 1 0 (by norm_num) u := Z.apply_symm_apply _
  have hR : Z R = boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u := Z.apply_symm_apply _
  rw [← hU,← hR,Z.inner_map_map,Z.inner_map_map] at h
  calc
    ⟪R,(a:SphereL2)⟫_ℝ = ⟪(a:SphereL2),R⟫_ℝ := real_inner_comm _ _
    _ = ⟪polynomialSphereL2 (pderiv i (harmonicPolynomialRepresentativeL sphereFischerInner k a)),U⟫_ℝ := h.symm
    _ = _ := real_inner_comm _ _

/-- The true flat L2 adjoint is the supplied harmonic raising graph on H1. -/
theorem coordinateBoundaryGradientAdjointL_graph (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u : SphereSobolev 1) :
    ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u)) ∈
      sphereRaisingGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let U := Z.symm (sphereSobolevInclusionL 1 0 (by norm_num) u)
  let R := Z.symm (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u)
  constructor
  · let q := sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics 0 R
    have h := coordinateBoundaryGradientAdjointL_single_test Q hQ i u 0 q
    rw [polynomialRepresentative_derivative_zero,inner_zero_right,
      inner_sphereHarmonicCoordinate_right orthogonalSphereHarmonics denseSphereHarmonics 0 R q] at h
    exact inner_self_eq_zero.mp h
  · intro k
    let q : harmonicSphereSubspace (k+1) := sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics (k+1) R-
      harmonicDerivativeAdjoint sphereFischerInner k i (sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k U)
    have h := coordinateBoundaryGradientAdjointL_single_test Q hQ i u (k+1) q
    rw [polynomialRepresentative_derivative,
      inner_sphereHarmonicCoordinate_right orthogonalSphereHarmonics denseSphereHarmonics (k+1) R q,
      inner_sphereHarmonicCoordinate_right orthogonalSphereHarmonics denseSphereHarmonics k U
        (harmonicDerivative sphereFischerInner k i q),← inner_harmonicDerivativeAdjoint] at h
    have hq : ⟪q,q⟫_ℝ = 0 := by
      dsimp only [q]
      rw [inner_sub_left]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hq)

end ShrinkingSpheres
