import Proof.FiniteAngularFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {α : Type*} {ι : α → Type*} [∀ i,Fintype (ι i)]

lemma fiberSq_finiteAngularField (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset α) (degree : α → ℕ) (hinj : Set.InjOn degree (s : Set α))
    (b : (i : α) → ι i → MvPolynomial I ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (degree i))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → X → ι i → ℝ) :
    fiberSq e y (fun w => finiteAngularField g e s b c d (y,w)) =
      ∑ i ∈ s,(normalizedFischerSquare (degree i) (finitePolynomialField (b i) (c i) y)+
        normalizedFischerSquare (degree i) (finitePolynomialField (b i) (d i) y)) := by
  change fiberSq e y (fun w => movingFrameComplexPolynomial g e
    (∑ i ∈ s,finitePolynomialField (b i) (c i) y) (∑ i ∈ s,finitePolynomialField (b i) (d i) y) (y,w)) = _
  exact fiberSq_movingFrameComplexPolynomial_family g e y hframe s degree hinj _ _
    (fun i hi => finitePolynomialField_homogeneous (b i) (hb i hi) (c i) y)
    (fun i hi => finitePolynomialField_homogeneous (b i) (hb i hi) (d i) y)
    (fun i hi => finitePolynomialField_harmonic (b i) (hΔ i hi) (c i) y)
    (fun i hi => finitePolynomialField_harmonic (b i) (hΔ i hi) (d i) y)

lemma sobolevSq_finiteAngularField (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (a : ℝ) (s : Finset α) (degree : α → ℕ) (hinj : Set.InjOn degree (s : Set α))
    (b : (i : α) → ι i → MvPolynomial I ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (degree i))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → X → ι i → ℝ) :
    sobolevSq g e a y (fun w => finiteAngularField g e s b c d (y,w)) =
      ∑ i ∈ s,(1+(degree i : ℝ))^(2*a)*(normalizedFischerSquare (degree i) (finitePolynomialField (b i) (c i) y)+
        normalizedFischerSquare (degree i) (finitePolynomialField (b i) (d i) y)) := by
  change sobolevSq g e a y (fun w => movingFrameComplexPolynomial g e
    (∑ i ∈ s,finitePolynomialField (b i) (c i) y) (∑ i ∈ s,finitePolynomialField (b i) (d i) y) (y,w)) = _
  exact sobolevSq_movingFrameComplexPolynomial_family g e y hframe a s degree hinj _ _
    (fun i hi => finitePolynomialField_homogeneous (b i) (hb i hi) (c i) y)
    (fun i hi => finitePolynomialField_homogeneous (b i) (hb i hi) (d i) y)
    (fun i hi => finitePolynomialField_harmonic (b i) (hΔ i hi) (c i) y)
    (fun i hi => finitePolynomialField_harmonic (b i) (hΔ i hi) (d i) y)

lemma fiberSq_finiteAngularField_horizontal {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset α) (degree : α → ℕ) (hpos : ∀ i ∈ s,1 ≤ degree i) (hinj : Set.InjOn degree (s : Set α))
    (b : (i : α) → ι i → MvPolynomial I ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (degree i))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → X → ι i → ℝ)
    (hc : ∀ i ∈ s,ContDiffOn ℝ ∞ (c i) Y) (hd : ∀ i ∈ s,ContDiffOn ℝ ∞ (d i) Y)
    {y : X} (hy : y ∈ Y) (j : I) :
    fiberSq e y (fun w => horizontal g (finiteAngularField g e s b c d) y w (e y j)) =
      ∑ i ∈ s,(normalizedFischerSquare (degree i) (covariantPolynomialDerivative g e (b i) (c i) y (e y j))+
        normalizedFischerSquare (degree i) (covariantPolynomialDerivative g e (b i) (d i) y (e y j))) := by
  have hfun : (fun w => horizontal g (finiteAngularField g e s b c d) y w (e y j)) =
      fun w => movingFrameComplexPolynomial g e (∑ i ∈ s,covariantPolynomialDerivative g e (b i) (c i) y (e y j))
        (∑ i ∈ s,covariantPolynomialDerivative g e (b i) (d i) y (e y j)) (y,w) := by
    funext w
    exact finiteAngularField_horizontal hY h hK e he hframe s b c d hc hd hy w (e y j)
  rw [hfun]
  exact fiberSq_movingFrameComplexPolynomial_family g e y (hframe y hy) s degree hinj _ _
    (fun i hi => covariantPolynomialDerivative_homogeneous (hpos i hi) g e (b i) (hb i hi) (c i) y (e y j))
    (fun i hi => covariantPolynomialDerivative_homogeneous (hpos i hi) g e (b i) (hb i hi) (d i) y (e y j))
    (fun i hi => covariantPolynomialDerivative_harmonic g e (b i) (hΔ i hi) (c i) y (e y j)
      (frameConnection_skew hY h hK e he hframe hy (e y j)))
    (fun i hi => covariantPolynomialDerivative_harmonic g e (b i) (hΔ i hi) (d i) y (e y j)
      (frameConnection_skew hY h hK e he hframe hy (e y j)))

lemma sobolevSq_finiteAngularField_horizontal {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (a : ℝ) (s : Finset α) (degree : α → ℕ) (hpos : ∀ i ∈ s,1 ≤ degree i) (hinj : Set.InjOn degree (s : Set α))
    (b : (i : α) → ι i → MvPolynomial I ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (degree i))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → X → ι i → ℝ)
    (hc : ∀ i ∈ s,ContDiffOn ℝ ∞ (c i) Y) (hd : ∀ i ∈ s,ContDiffOn ℝ ∞ (d i) Y)
    {y : X} (hy : y ∈ Y) (j : I) :
    sobolevSq g e a y (fun w => horizontal g (finiteAngularField g e s b c d) y w (e y j)) =
      ∑ i ∈ s,(1+(degree i : ℝ))^(2*a)*
        (normalizedFischerSquare (degree i) (covariantPolynomialDerivative g e (b i) (c i) y (e y j))+
          normalizedFischerSquare (degree i) (covariantPolynomialDerivative g e (b i) (d i) y (e y j))) := by
  have hfun : (fun w => horizontal g (finiteAngularField g e s b c d) y w (e y j)) =
      fun w => movingFrameComplexPolynomial g e (∑ i ∈ s,covariantPolynomialDerivative g e (b i) (c i) y (e y j))
        (∑ i ∈ s,covariantPolynomialDerivative g e (b i) (d i) y (e y j)) (y,w) := by
    funext w
    exact finiteAngularField_horizontal hY h hK e he hframe s b c d hc hd hy w (e y j)
  rw [hfun]
  exact sobolevSq_movingFrameComplexPolynomial_family g e y (hframe y hy) a s degree hinj _ _
    (fun i hi => covariantPolynomialDerivative_homogeneous (hpos i hi) g e (b i) (hb i hi) (c i) y (e y j))
    (fun i hi => covariantPolynomialDerivative_homogeneous (hpos i hi) g e (b i) (hb i hi) (d i) y (e y j))
    (fun i hi => covariantPolynomialDerivative_harmonic g e (b i) (hΔ i hi) (c i) y (e y j)
      (frameConnection_skew hY h hK e he hframe hy (e y j)))
    (fun i hi => covariantPolynomialDerivative_harmonic g e (b i) (hΔ i hi) (d i) y (e y j)
      (frameConnection_skew hY h hK e he hframe hy (e y j)))

end ShrinkingSpheres
