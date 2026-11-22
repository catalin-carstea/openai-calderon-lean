module

public import Proof.CalderonN.FiniteTensorFields
public import Proof.CalderonN.FischerCurvatureBound
import Mathlib.Tactic

@[expose] public section

/- Port of IntegratedFischerFields.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set MeasureTheory MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

lemma weightedPolynomialDerivative_zero_outside (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s : ℝ)
    {y : (X n)} (hy : y ∉ tsupport c) (a : (X n)) : weightedPolynomialDerivative g e b c f k s y a = 0 := by
  simp [weightedPolynomialDerivative, covariantPolynomialDerivative_zero_outside g e b c hy,
    finitePolynomialField_zero_outside b c hy]

lemma weightedCovectorPolynomialDerivative_zero_outside (g : (MetricField n)) (e : (Frame n))
    (b : ι → (I n) → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s : ℝ)
    {y : (X n)} (hy : y ∉ tsupport c) (a : (X n)) (i : (I n)) :
    weightedCovectorPolynomialDerivative g e b c f k s y a i = 0 := by
  simp [weightedCovectorPolynomialDerivative, covectorPolynomialDerivative_zero_outside g e b c hy,
    finitePolynomialField_zero_outside _ c hy]

lemma weightedTensorPolynomialDerivative_zero_outside (g : (MetricField n)) (e : (Frame n))
    (b : ι → (I n) → (I n) → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s : ℝ)
    {y : (X n)} (hy : y ∉ tsupport c) (a : (X n)) (i j : (I n)) :
    weightedTensorPolynomialDerivative g e b c f k s y a i j = 0 := by
  simp [weightedTensorPolynomialDerivative, tensorPolynomialDerivative,
    covectorPolynomialDerivative_zero_outside g e _ c hy, finitePolynomialField_zero_outside _ c hy]

def loweredWeightedTensorPolynomialFamily (b : ι → MvPolynomial (I n) ℝ) :
    ((I n) × ((ι ⊕ ((I n) × (I n) × ι)) ⊕ ι)) → (I n) → (I n) → MvPolynomial (I n) ℝ :=
  fun a i j => pderiv j (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a i)

def loweredWeightedTensorCoefficientFamily (g : (MetricField n)) (e : (Frame n)) (c : (X n) → ι → ℝ)
    (f : (X n) → ℝ) (k t : ℝ) : (X n) → ((I n) × ((ι ⊕ ((I n) × (I n) × ι)) ⊕ ι)) → ℝ :=
  indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)

def loweredWeightedTensorField (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) (y : (X n)) (i j : (I n)) : MvPolynomial (I n) ℝ :=
  weightedCovectorPolynomialDerivative g e (fun a h => pderiv h (b a)) c f k t y (e y i) j

lemma loweredWeightedTensorField_eq_finite (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) (y : (X n)) (i j : (I n)) :
    loweredWeightedTensorField g e b c f k t y i j =
      finitePolynomialField (fun a => loweredWeightedTensorPolynomialFamily b a i j)
        (loweredWeightedTensorCoefficientFamily g e c f k t) y :=
  (finitePolynomialField_weighted_lowered g e b c f k t y i j).symm

def loweredWeightedTraceField (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) (y : (X n)) : MvPolynomial (I n) ℝ :=
  ∑ i, loweredWeightedTensorField g e b c f k t y i i

lemma loweredWeightedTraceField_eq_finite (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) (y : (X n)) :
    loweredWeightedTraceField g e b c f k t y =
      finitePolynomialField (weightedTracePolynomialFamily b) (loweredWeightedTensorCoefficientFamily g e c f k t) y :=
  (finitePolynomialField_weighted_trace g e b c f k t y).symm

def loweredWeightedSecondTensorField (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s t : ℝ) (y : (X n)) (i j l : (I n)) : MvPolynomial (I n) ℝ :=
  weightedTensorPolynomialDerivative g e (loweredWeightedTensorPolynomialFamily b)
    (loweredWeightedTensorCoefficientFamily g e c f k t) f k s y (e y i) j l

lemma loweredWeightedSecondTensorField_eq_indexed {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : (X n)} (hy : y ∈ Ω) (i j l : (I n)) :
    loweredWeightedSecondTensorField g e b c f k s t y i j l =
      weightedLoweredIndexedHessian g e b c f k s t y i j l :=
  weightedTensorPolynomialDerivative_weighted_lowered hΩ h hK e he hframe b c f k s t hc hf hy i j l

lemma loweredWeightedSecondTensorField_zero_outside (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s t : ℝ)
    {y : (X n)} (hy : y ∉ tsupport c) (i j l : (I n)) :
    loweredWeightedSecondTensorField g e b c f k s t y i j l = 0 :=
  weightedTensorPolynomialDerivative_zero_outside g e _ _ f k s
    (fun ht => hy (weightedIndexed_flat_tsupport g e c f k t ht)) _ j l

lemma loweredWeightedSecondTensorField_trace {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s t : ℝ)
    {y : (X n)} (hy : y ∈ Ω) (j : (I n)) :
    (∑ i, loweredWeightedSecondTensorField g e b c f k s t y j i i) =
      weightedPolynomialDerivative g e (weightedTracePolynomialFamily b)
        (loweredWeightedTensorCoefficientFamily g e c f k t) f k s y (e y j) :=
  (weightedPolynomialDerivative_tensorTrace hΩ h hK e he hframe (loweredWeightedTensorPolynomialFamily b)
    (loweredWeightedTensorCoefficientFamily g e c f k t) f k s hy (e y j)).symm

def loweredWeightedCrossEnergy (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) : ℝ :=
  ∫ y, metricDensity g y * ∑ i, ∑ j, fischerInner (loweredWeightedTensorField g e b c f k t y i j)
    (loweredWeightedTensorField g e b c f k t y j i)

def loweredWeightedTraceSquare (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ) : ℝ :=
  ∫ y, metricDensity g y * fischerInner (loweredWeightedTraceField g e b c f k t y)
    (loweredWeightedTraceField g e b c f k t y)

theorem loweredWeightedCrossEnergy_adjoint {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    loweredWeightedCrossEnergy g e b c f k t =
      ∫ y, metricDensity g y * ∑ i, ∑ j, fischerInner (pderiv j (finitePolynomialField b c y))
        (loweredWeightedSecondTensorField g e b c f k (-t) t y i j i) := by
  have hflat := weightedIndexed_flat_smooth_compact hΩ h hK e he c f k t hc hf hcompact hsupp
  have hh := compact_contracted_weighted_tensor_fischer_adjoint hΩ h hK e he hframe
    (fun a j => pderiv j (b a)) (fun a i j => loweredWeightedTensorPolynomialFamily b a j i)
    c (loweredWeightedTensorCoefficientFamily g e c f k t) f k t hc hflat.1 hf hcompact hsupp
  convert hh using 1
  · apply integral_congr_ae
    filter_upwards [] with y
    simp_rw [← loweredWeightedTensorField_eq_finite]
    rfl
  · apply integral_congr_ae
    filter_upwards [] with y
    simp_rw [weightedTensorPolynomialDerivative_transpose, finitePolynomialField_partial]
    rfl

theorem loweredWeightedTraceSquare_adjoint {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    loweredWeightedTraceSquare g e b c f k t =
      ∫ y, metricDensity g y * ∑ j, ∑ i, fischerInner (pderiv j (finitePolynomialField b c y))
        (loweredWeightedSecondTensorField g e b c f k (-t) t y j i i) := by
  have hflat := weightedIndexed_flat_smooth_compact hΩ h hK e he c f k t hc hf hcompact hsupp
  have hh := compact_contracted_weighted_covector_fischer_adjoint hΩ h hK e he hframe
    (weightedTracePolynomialFamily b) (fun a j => pderiv j (b a))
    (loweredWeightedTensorCoefficientFamily g e c f k t) c f k (-t) hflat.1 hc hf hflat.2.1 (hflat.2.2.trans hsupp)
  have hr : (∫ y, metricDensity g y * ∑ j, fischerInner
      (finitePolynomialField (weightedTracePolynomialFamily b) (loweredWeightedTensorCoefficientFamily g e c f k t) y)
      (weightedCovectorPolynomialDerivative g e (fun a j => pderiv j (b a)) c f k (- -t) y (e y j) j)) =
      loweredWeightedTraceSquare g e b c f k t := by
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [neg_neg, ← loweredWeightedTraceField_eq_finite,
      loweredWeightedTraceField, loweredWeightedTensorField, ← fischerInner_sum_right]
  rw [hr] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Ω
  · simp_rw [← fischerInner_sum_right, loweredWeightedSecondTensorField_trace hΩ h hK e he hframe b c f k (-t) t hy,
      finitePolynomialField_partial, fischerInner_symm]
  · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
    have houtFlat : y ∉ tsupport (loweredWeightedTensorCoefficientFamily g e c f k t) :=
      fun ht => hout (hflat.2.2 ht)
    simp [weightedPolynomialDerivative_zero_outside g e _ _ f k (-t) houtFlat,
      loweredWeightedSecondTensorField_zero_outside g e b c f k (-t) t hout,
      fischerInner_zero_right, fischerInner_zero_left]

end CalderonN
