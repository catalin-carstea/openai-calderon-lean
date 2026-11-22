module

public import Proof.CalderonN.HorizontalComponents
public import Proof.CalderonN.ComplexFiniteFields
public import Proof.CalderonN.ComplexZonalProjection

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 10
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

lemma harmonicProjectionPolynomial_eq_of_Lp (k : ℕ) (u : (SphereL2 N))
    (p : MvPolynomial (I N) ℝ) (hp : p ∈ harmonicHomogeneous N k)
    (hrep : polynomialSphereL2 p = (harmonicProjection k u : (SphereL2 N))) :
    (harmonicProjectionPolynomial k u).val = p := by
  apply (polynomialSphereL2_injective_degree (sphereFischerInner N) k _ _
    (harmonicProjectionPolynomial k u).property hp).mp
  rw [polynomialSphereL2_harmonicProjectionPolynomial,hrep]

/-- Projection followed by actual horizontal differentiation agrees with the literal kernel
    projection of the physical horizontal derivative. Real/imaginary coordinates share one
    finite harmonic family, as required by the finite coercivity theorem. -/
theorem horizontal_projection_commutes (hn : 3 ≤ N) {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ : (Field N)) (hφ : smoothNear φ (bundle Y g)) (G : (X N) × (X N) → ℂ) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : (UnitSphere N),G (y,v.val) = φ (y,frameVector e y v.val))
    {ι : Type*} [Fintype ι] {k : ℕ} (hk : 1 ≤ k)
    (b : ι → MvPolynomial (I N) ℝ) (hb : ∀ j,b j ∈ harmonicHomogeneous N k)
    (c d : (X N) → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hcrep : ∀ y,polynomialSphereL2 (finitePolynomialField b c y) =
      (harmonicProjection k (ambientSphereL2 (fun p => (G p).re) (Complex.reCLM.contDiff.comp hG) y) : (SphereL2 N)))
    (hdrep : ∀ y,polynomialSphereL2 (finitePolynomialField b d y) =
      (harmonicProjection k (ambientSphereL2 (fun p => (G p).im) (Complex.imCLM.contDiff.comp hG) y) : (SphereL2 N)))
    {y : (X N)} (hy : y ∈ Y) (a : (X N)) (HRe HIm : (SphereL2 N))
    (hHRe : HRe =ᵐ[(sphereProbability N)] (fun v : (UnitSphere N) => (horizontal g φ y (frameVector e y v.val) a).re))
    (hHIm : HIm =ᵐ[(sphereProbability N)] (fun v : (UnitSphere N) => (horizontal g φ y (frameVector e y v.val) a).im))
    (v : (UnitSphere N)) :
    horizontal g (pairedPolynomialField g e b c d) y (frameVector e y v.val) a =
      degreePart g e k y (fun w => horizontal g φ y w a) (frameVector e y v.val) := by
  have hsk := frameConnection_skew hY h hK e he hframe hy a
  have hpc : covariantPolynomialDerivative g e b c y a ∈ harmonicHomogeneous N k :=
    ⟨covariantPolynomialDerivative_homogeneous hk g e b (fun j => (hb j).1) c y a,
      covariantPolynomialDerivative_harmonic g e b (fun j => (hb j).2) c y a hsk⟩
  have hpd : covariantPolynomialDerivative g e b d y a ∈ harmonicHomogeneous N k :=
    ⟨covariantPolynomialDerivative_homogeneous hk g e b (fun j => (hb j).1) d y a,
      covariantPolynomialDerivative_harmonic g e b (fun j => (hb j).2) d y a hsk⟩
  have hUc : ContDiff ℝ ∞ (fun y => harmonicProjection k
      (ambientSphereL2 (fun p => (G p).re) (Complex.reCLM.contDiff.comp hG) y)) :=
    (harmonicProjection k).contDiff.comp (contDiff_ambientSphereL2 _ _)
  have hUd : ContDiff ℝ ∞ (fun y => harmonicProjection k
      (ambientSphereL2 (fun p => (G p).im) (Complex.imCLM.contDiff.comp hG) y)) :=
    (harmonicProjection k).contDiff.comp (contDiff_ambientSphereL2 _ _)
  have hclp : polynomialSphereL2 (covariantPolynomialDerivative g e b c y a) = (harmonicProjection k HRe : (SphereL2 N)) := by
    rw [polynomialSphereL2_covariantDerivative hY h hK e he hframe k b hb c _ hc hUc hcrep hy a,
      harmonicProjection_horizontal_component hY h hK e he hframe φ hφ G hG hrep Complex.reCLM hy a HRe hHRe k]
    rfl
  have hdlp : polynomialSphereL2 (covariantPolynomialDerivative g e b d y a) = (harmonicProjection k HIm : (SphereL2 N)) := by
    rw [polynomialSphereL2_covariantDerivative hY h hK e he hframe k b hb d _ hd hUd hdrep hy a,
      harmonicProjection_horizontal_component hY h hK e he hframe φ hφ G hG hrep Complex.imCLM hy a HIm hHIm k]
    rfl
  rw [degreePart_harmonicProjection_components hn g e y (hframe y hy) (fun w => horizontal g φ y w a) HRe HIm hHRe hHIm v k,
    harmonicProjectionPolynomial_eq_of_Lp k HRe _ hpc hclp,harmonicProjectionPolynomial_eq_of_Lp k HIm _ hpd hdlp,
    pairedPolynomialField_horizontal hY h hK e he hframe b c d hc.contDiffOn hd.contDiffOn hy,
    movingFrameComplexPolynomial_frameVector g e y (hframe y hy)]

end CalderonN
