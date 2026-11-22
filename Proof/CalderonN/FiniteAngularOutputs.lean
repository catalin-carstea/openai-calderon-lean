module

public import Proof.CalderonN.FiniteAngularEnergy

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.AngularPolynomial

variable {α : Type*} {ι : α → Type*} [∀ i,Fintype (ι i)]

def finiteRaisedField (g : (MetricField N)) (e : (Frame N)) (s : Finset α) (index : α → ℕ)
    (b : (i : α) → ι i → MvPolynomial (I N) ℝ) (c d : (i : α) → (X N) → ι i → ℝ) (f : (X N) → ℝ) : (Field N) := fun z =>
  movingFrameComplexPolynomial g e (∑ i ∈ s,raisedPolynomialField g e (b i) (c i) f (index i) z.1)
    (∑ i ∈ s,raisedPolynomialField g e (b i) (d i) f (index i) z.1) z

def finiteLoweredField (g : (MetricField N)) (e : (Frame N)) (s : Finset α) (index : α → ℕ)
    (b : (i : α) → ι i → MvPolynomial (I N) ℝ) (c d : (i : α) → (X N) → ι i → ℝ) (f : (X N) → ℝ) : (Field N) := fun z =>
  movingFrameComplexPolynomial g e (∑ i ∈ s,loweredPolynomialField g e (b i) (c i) f (index i) z.1)
    (∑ i ∈ s,loweredPolynomialField g e (b i) (d i) f (index i) z.1) z

lemma fiberSq_finiteRaisedField {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset α) (index : α → ℕ) (hinj : Set.InjOn index (s : Set α))
    (b : (i : α) → ι i → MvPolynomial (I N) ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (index i+1))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → (X N) → ι i → ℝ) (f : (X N) → ℝ)
    {y : (X N)} (hy : y ∈ Y) :
    fiberSq e y (fun w => finiteRaisedField g e s index b c d f (y,w)) =
      ∑ i ∈ s,(normalizedFischerSquare (index i+2) (raisedPolynomialField g e (b i) (c i) f (index i) y)+
        normalizedFischerSquare (index i+2) (raisedPolynomialField g e (b i) (d i) f (index i) y)) := by
  have hinj' : Set.InjOn (fun i => index i+2) (s : Set α) := by
    intro i hi j hj hd
    apply hinj hi hj
    change index i+2 = index j+2 at hd
    omega
  change fiberSq e y (fun w => movingFrameComplexPolynomial g e
    (∑ i ∈ s,raisedPolynomialField g e (b i) (c i) f (index i) y)
    (∑ i ∈ s,raisedPolynomialField g e (b i) (d i) f (index i) y) (y,w)) = _
  exact fiberSq_movingFrameComplexPolynomial_family g e y (hframe y hy) s (fun i => index i+2) hinj' _ _
    (fun i hi => raisedPolynomialField_homogeneous g e (index i) (b i) (hb i hi) (c i) f y)
    (fun i hi => raisedPolynomialField_homogeneous g e (index i) (b i) (hb i hi) (d i) f y)
    (fun i hi => raisedPolynomialField_harmonic hY h hK e he hframe (index i) (b i) (hb i hi) (hΔ i hi) (c i) f hy)
    (fun i hi => raisedPolynomialField_harmonic hY h hK e he hframe (index i) (b i) (hb i hi) (hΔ i hi) (d i) f hy)

lemma fiberSq_finiteLoweredField {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset α) (index : α → ℕ) (hinj : Set.InjOn index (s : Set α))
    (b : (i : α) → ι i → MvPolynomial (I N) ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (index i+1))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → (X N) → ι i → ℝ) (f : (X N) → ℝ)
    {y : (X N)} (hy : y ∈ Y) :
    fiberSq e y (fun w => finiteLoweredField g e s index b c d f (y,w)) =
      ∑ i ∈ s,(normalizedFischerSquare (index i) (loweredPolynomialField g e (b i) (c i) f (index i) y)+
        normalizedFischerSquare (index i) (loweredPolynomialField g e (b i) (d i) f (index i) y)) := by
  change fiberSq e y (fun w => movingFrameComplexPolynomial g e
    (∑ i ∈ s,loweredPolynomialField g e (b i) (c i) f (index i) y)
    (∑ i ∈ s,loweredPolynomialField g e (b i) (d i) f (index i) y) (y,w)) = _
  exact fiberSq_movingFrameComplexPolynomial_family g e y (hframe y hy) s index hinj _ _
    (fun i hi => loweredPolynomialField_homogeneous g e (index i) (b i) (hb i hi) (c i) f y)
    (fun i hi => loweredPolynomialField_homogeneous g e (index i) (b i) (hb i hi) (d i) f y)
    (fun i hi => loweredPolynomialField_harmonic hY h hK e he hframe (index i) (b i) (hΔ i hi) (c i) f hy)
    (fun i hi => loweredPolynomialField_harmonic hY h hK e he hframe (index i) (b i) (hΔ i hi) (d i) f hy)

/-- Physical output Pythagoras for a finite sum of raising fields. -/
theorem outputSq_finiteRaisedField {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset α) (index : α → ℕ) (hinj : Set.InjOn index (s : Set α))
    (b : (i : α) → ι i → MvPolynomial (I N) ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (index i+1))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → (X N) → ι i → ℝ)
    (hc : ∀ i ∈ s,ContDiff ℝ ∞ (c i)) (hd : ∀ i ∈ s,ContDiff ℝ ∞ (d i))
    (hcompactc : ∀ i ∈ s,HasCompactSupport (c i)) (hcompactd : ∀ i ∈ s,HasCompactSupport (d i))
    (hsuppc : ∀ i ∈ s,tsupport (c i) ⊆ Y) (hsuppd : ∀ i ∈ s,tsupport (d i) ⊆ Y)
    (f : (X N) → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    outputSq Y g e (finiteRaisedField g e s index b c d f) =
      ∑ i ∈ s,outputSq Y g e (pairedRaisedField g e (b i) (c i) (d i) f (index i)) := by
  have hI (i : α) (hi : i ∈ s) : Integrable (fun y => metricDensity g y *
      (normalizedFischerSquare (index i+2) (raisedPolynomialField g e (b i) (c i) f (index i) y)+
        normalizedFischerSquare (index i+2) (raisedPolynomialField g e (b i) (d i) f (index i) y))) := by
    have hh := (integrable_fischerRaisingEnergy hY h hK e he (b i) (c i) f (index i) (hc i hi) hf (hcompactc i hi) (hsuppc i hi)).add
      (integrable_fischerRaisingEnergy hY h hK e he (b i) (d i) f (index i) (hd i hi) hf (hcompactd i hi) (hsuppd i hi))
    apply hh.congr
    filter_upwards [] with y
    change metricDensity g y * _ + metricDensity g y * _ = metricDensity g y * (_ + _)
    ring
  rw [outputSq]
  change (∫ y in Y,metricDensity g y * fiberSq e y (fun w => finiteRaisedField g e s index b c d f (y,w))) = _
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy => congrArg (metricDensity g y * ·)
    (fiberSq_finiteRaisedField hY h hK e he hframe s index hinj b hb hΔ c d f hy))]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum s (fun i hi => (hI i hi).integrableOn)]
  apply Finset.sum_congr rfl
  intro i hi
  unfold outputSq pairedRaisedField
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  exact congrArg (metricDensity g y * ·)
    (fiberSq_movingFrameComplexPolynomial g e y (hframe y hy) _ _
      (raisedPolynomialField_homogeneous g e (index i) (b i) (hb i hi) (c i) f y)
      (raisedPolynomialField_homogeneous g e (index i) (b i) (hb i hi) (d i) f y)
      (raisedPolynomialField_harmonic hY h hK e he hframe (index i) (b i) (hb i hi) (hΔ i hi) (c i) f hy)
      (raisedPolynomialField_harmonic hY h hK e he hframe (index i) (b i) (hb i hi) (hΔ i hi) (d i) f hy)).symm

/-- Physical output Pythagoras for a finite sum of lowering fields. -/
theorem outputSq_finiteLoweredField {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset α) (index : α → ℕ) (hinj : Set.InjOn index (s : Set α))
    (b : (i : α) → ι i → MvPolynomial (I N) ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (index i+1))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → (X N) → ι i → ℝ)
    (hc : ∀ i ∈ s,ContDiff ℝ ∞ (c i)) (hd : ∀ i ∈ s,ContDiff ℝ ∞ (d i))
    (hcompactc : ∀ i ∈ s,HasCompactSupport (c i)) (hcompactd : ∀ i ∈ s,HasCompactSupport (d i))
    (hsuppc : ∀ i ∈ s,tsupport (c i) ⊆ Y) (hsuppd : ∀ i ∈ s,tsupport (d i) ⊆ Y)
    (f : (X N) → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    outputSq Y g e (finiteLoweredField g e s index b c d f) =
      ∑ i ∈ s,outputSq Y g e (pairedLoweredField g e (b i) (c i) (d i) f (index i)) := by
  have hI (i : α) (hi : i ∈ s) : Integrable (fun y => metricDensity g y *
      (normalizedFischerSquare (index i) (loweredPolynomialField g e (b i) (c i) f (index i) y)+
        normalizedFischerSquare (index i) (loweredPolynomialField g e (b i) (d i) f (index i) y))) := by
    have hh := (integrable_fischerLoweringEnergy hY h hK e he (b i) (c i) f (index i) (hc i hi) hf (hcompactc i hi) (hsuppc i hi)).add
      (integrable_fischerLoweringEnergy hY h hK e he (b i) (d i) f (index i) (hd i hi) hf (hcompactd i hi) (hsuppd i hi))
    apply hh.congr
    filter_upwards [] with y
    change metricDensity g y * _ + metricDensity g y * _ = metricDensity g y * (_ + _)
    ring
  rw [outputSq]
  change (∫ y in Y,metricDensity g y * fiberSq e y (fun w => finiteLoweredField g e s index b c d f (y,w))) = _
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy => congrArg (metricDensity g y * ·)
    (fiberSq_finiteLoweredField hY h hK e he hframe s index hinj b hb hΔ c d f hy))]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum s (fun i hi => (hI i hi).integrableOn)]
  apply Finset.sum_congr rfl
  intro i hi
  unfold outputSq pairedLoweredField
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  exact congrArg (metricDensity g y * ·)
    (fiberSq_movingFrameComplexPolynomial g e y (hframe y hy) _ _
      (loweredPolynomialField_homogeneous g e (index i) (b i) (hb i hi) (c i) f y)
      (loweredPolynomialField_homogeneous g e (index i) (b i) (hb i hi) (d i) f y)
      (loweredPolynomialField_harmonic hY h hK e he hframe (index i) (b i) (hΔ i hi) (c i) f hy)
      (loweredPolynomialField_harmonic hY h hK e he hframe (index i) (b i) (hΔ i hi) (d i) f hy)).symm

end CalderonN
