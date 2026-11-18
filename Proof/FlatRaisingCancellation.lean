import Proof.FlatAngularShiftIdentification

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
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SphereDerivativeAdjoint

/-- A single harmonic mode is raised by the actual flat boundary adjoint. -/
theorem coordinateBoundaryGradientAdjointL_single (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (k : ℕ) (a : harmonicSphereSubspace k) :
    boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL
      (sphereSobolevSingleL 1 k a) =
      sphereSobolevSingleL 0 (k+1) (harmonicDerivativeAdjoint sphereFischerInner k i a) := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have h := coordinateBoundaryGradientAdjointL_graph Q hQ i (sphereSobolevSingleL 1 k a)
  rw [sphereSobolevInclusionL_single,← zeroEquiv_harmonic_subtype,Z.symm_apply_apply] at h
  have hOutput := sphereRaisingGraph_output_unique sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
    (a:SphereL2) _ _ h
      (sphereRaisingGraph_single sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i k a)
  have hZ := congrArg Z hOutput
  exact (Z.apply_symm_apply _).symm.trans (hZ.trans (zeroEquiv_harmonic_subtype _ _))

/-- The supplied polynomial cancellation holds for the induced harmonic
    Hilbert-space operators on every degree, including degree zero. -/
theorem sum_double_harmonicDerivativeAdjoint_zero (k : ℕ) (a : harmonicSphereSubspace k) :
    (∑ i : I,(harmonicDerivativeAdjoint sphereFischerInner (k+1) i
      (harmonicDerivativeAdjoint sphereFischerInner k i a) : SphereL2)) = 0 := by
  obtain ⟨p,hp⟩ := harmonicPolynomialSphereMap_surjective k a
  have hTerm (i : I) :
      (harmonicDerivativeAdjoint sphereFischerInner (k+1) i
        (harmonicDerivativeAdjoint sphereFischerInner k i a) : SphereL2) =
      polynomialSphereL2 (sphereDerivativeAdjoint (k+1) i (sphereDerivativeAdjoint k i p)) := by
    rw [← hp,harmonicDerivativeAdjoint_apply_image]
    let q : harmonicHomogeneous (k+1) :=
      ⟨sphereDerivativeAdjoint k i p,sphereDerivativeAdjoint_harmonicHomogeneous k i p p.property⟩
    have hInput : harmonicPolynomialDerivativeAdjointMap k i p = harmonicPolynomialSphereMap (k+1) q := rfl
    rw [hInput,harmonicDerivativeAdjoint_apply_image]
    rfl
  have hPoly := congrArg polynomialSphereL2 (sum_double_sphereDerivativeAdjoint_eq_zero sphereFischerInner k p p.property)
  rw [map_sum,map_zero] at hPoly
  exact (Finset.sum_congr rfl (fun i _ => hTerm i)).trans hPoly

/-- Contracting two consecutive raising actions gives zero on the full closed
    graph domain. Thus the leading double-raising term cancels before estimates. -/
theorem sphereRaisingGraph_contracted_double_zero (u : SphereL2) (v w : I → SphereL2)
    (hv : ∀ i,(u,v i) ∈ sphereRaisingGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i)
    (hw : ∀ i,(v i,w i) ∈ sphereRaisingGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i) :
    (∑ i : I,w i) = 0 := by
  apply (sphereHarmonicDecomposition orthogonalSphereHarmonics denseSphereHarmonics).injective
  apply lp.ext
  funext m
  change sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics m (∑ i : I,w i) =
    sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics m 0
  rw [map_sum,map_zero]
  cases m with
  | zero => simp only [(hw _).1,Finset.sum_const_zero]
  | succ m =>
    cases m with
    | zero => simp only [(hw _).2 0,(hv _).1,map_zero,Finset.sum_const_zero]
    | succ k =>
      simp only [(hw _).2 (k+1),(hv _).2 k]
      apply Subtype.ext
      change (∑ i : I,(harmonicDerivativeAdjoint sphereFischerInner (k+1) i
        (harmonicDerivativeAdjoint sphereFischerInner k i
          (sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k u)) : SphereL2)) = 0
      exact sum_double_harmonicDerivativeAdjoint_zero k _

end ShrinkingSpheres
