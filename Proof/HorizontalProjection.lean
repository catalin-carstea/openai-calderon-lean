import Proof.HorizontalComponents
import Proof.ComplexFiniteFields
import Proof.ComplexHilbertProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 10
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SpectralCoreRegularity

lemma harmonicProjectionPolynomial_eq_of_Lp (k : ℕ) (u : SphereL2)
    (p : MvPolynomial I ℝ) (hp : p ∈ harmonicHomogeneous k)
    (hrep : polynomialSphereL2 p = (harmonicProjection k u : SphereL2)) :
    (harmonicProjectionPolynomial k u).val = p := by
  apply (polynomialSphereL2_injective_degree sphereFischerInner k _ _
    (harmonicProjectionPolynomial k u).property hp).mp
  rw [polynomialSphereL2_harmonicProjectionPolynomial,hrep]

/-- Projection followed by actual horizontal differentiation agrees with the literal kernel
    projection of the physical horizontal derivative. Real/imaginary coordinates share one
    finite harmonic family, as required by the finite coercivity theorem. -/
theorem horizontal_projection_commutes {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ : Field) (hφ : smoothNear φ (bundle Y g)) (G : X × X → ℂ) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : UnitSphere,G (y,v.val) = φ (y,frameVector e y v.val))
    {ι : Type*} [Fintype ι] {k : ℕ} (hk : 1 ≤ k)
    (b : ι → MvPolynomial I ℝ) (hb : ∀ j,b j ∈ harmonicHomogeneous k)
    (c d : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hcrep : ∀ y,polynomialSphereL2 (finitePolynomialField b c y) =
      (harmonicProjection k (ambientSphereL2 (fun p => (G p).re) (Complex.reCLM.contDiff.comp hG) y) : SphereL2))
    (hdrep : ∀ y,polynomialSphereL2 (finitePolynomialField b d y) =
      (harmonicProjection k (ambientSphereL2 (fun p => (G p).im) (Complex.imCLM.contDiff.comp hG) y) : SphereL2))
    {y : X} (hy : y ∈ Y) (a : X) (HRe HIm : SphereL2)
    (hHRe : HRe =ᵐ[sphereProbability] (fun v : UnitSphere => (horizontal g φ y (frameVector e y v.val) a).re))
    (hHIm : HIm =ᵐ[sphereProbability] (fun v : UnitSphere => (horizontal g φ y (frameVector e y v.val) a).im))
    (v : UnitSphere) :
    horizontal g (pairedPolynomialField g e b c d) y (frameVector e y v.val) a =
      degreePart g e k y (fun w => horizontal g φ y w a) (frameVector e y v.val) := by
  have hsk := frameConnection_skew hY h hK e he hframe hy a
  have hpc : covariantPolynomialDerivative g e b c y a ∈ harmonicHomogeneous k :=
    ⟨covariantPolynomialDerivative_homogeneous hk g e b (fun j => (hb j).1) c y a,
      covariantPolynomialDerivative_harmonic g e b (fun j => (hb j).2) c y a hsk⟩
  have hpd : covariantPolynomialDerivative g e b d y a ∈ harmonicHomogeneous k :=
    ⟨covariantPolynomialDerivative_homogeneous hk g e b (fun j => (hb j).1) d y a,
      covariantPolynomialDerivative_harmonic g e b (fun j => (hb j).2) d y a hsk⟩
  have hUc : ContDiff ℝ ∞ (fun y => harmonicProjection k
      (ambientSphereL2 (fun p => (G p).re) (Complex.reCLM.contDiff.comp hG) y)) :=
    (harmonicProjection k).contDiff.comp (contDiff_ambientSphereL2 _ _)
  have hUd : ContDiff ℝ ∞ (fun y => harmonicProjection k
      (ambientSphereL2 (fun p => (G p).im) (Complex.imCLM.contDiff.comp hG) y)) :=
    (harmonicProjection k).contDiff.comp (contDiff_ambientSphereL2 _ _)
  have hclp : polynomialSphereL2 (covariantPolynomialDerivative g e b c y a) = (harmonicProjection k HRe : SphereL2) := by
    rw [polynomialSphereL2_covariantDerivative hY h hK e he hframe k b hb c _ hc hUc hcrep hy a,
      harmonicProjection_horizontal_component hY h hK e he hframe φ hφ G hG hrep Complex.reCLM hy a HRe hHRe k]
    rfl
  have hdlp : polynomialSphereL2 (covariantPolynomialDerivative g e b d y a) = (harmonicProjection k HIm : SphereL2) := by
    rw [polynomialSphereL2_covariantDerivative hY h hK e he hframe k b hb d _ hd hUd hdrep hy a,
      harmonicProjection_horizontal_component hY h hK e he hframe φ hφ G hG hrep Complex.imCLM hy a HIm hHIm k]
    rfl
  rw [degreePart_harmonicProjection_components g e y (hframe y hy) _ HRe HIm hHRe hHIm v k,
    harmonicProjectionPolynomial_eq_of_Lp k HRe _ hpc hclp,harmonicProjectionPolynomial_eq_of_Lp k HIm _ hpd hdlp,
    pairedPolynomialField_horizontal hY h hK e he hframe b c d hc.contDiffOn hd.contDiffOn hy,
    movingFrameComplexPolynomial_frameVector g e y (hframe y hy)]

end ShrinkingSpheres
