module

public import Proof.CalderonN.ProfileConvexity
import Mathlib.Tactic

@[expose] public section

/- Port of FiniteFockEnergy.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set MeasureTheory MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

def polynomialSphereRaising (m : ℕ) (q : (I n) → MvPolynomial (I n) ℝ) : MvPolynomial (I n) ℝ :=
  C ((n:ℝ)+2*((m:ℝ)+1)) * harmonicRaising m q

lemma polynomialSphereRaising_sum_family {J : Type*} [Fintype J] (m : ℕ) (q : J → (I n) → MvPolynomial (I n) ℝ) :
    polynomialSphereRaising m (fun i => ∑ a, q a i) = ∑ a, polynomialSphereRaising m (q a) := by
  simp only [polynomialSphereRaising, harmonicRaising, polynomialRaising, polynomialDivergence,
    map_sum]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) Finset.sum_comm Finset.sum_comm

lemma polynomialSphereRaising_C_mul_family (m : ℕ) (q : (I n) → MvPolynomial (I n) ℝ) (a : ℝ) :
    polynomialSphereRaising m (fun i => C a * q i) = C a * polynomialSphereRaising m q := by
  simp only [polynomialSphereRaising, harmonicRaising, polynomialRaising, polynomialDivergence,
    pderiv_C_mul]
  have hR : (∑ i, MvPolynomial.X i * (C a * q i)) =
      C a * ∑ i, MvPolynomial.X i * q i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR, ← Finset.mul_sum Finset.univ (fun i => pderiv i (q i)) (C a)]
  ring

variable {ι : Type*} [Fintype ι]

lemma polynomialSphereRaising_finitePolynomialField (m : ℕ) (b : ι → (I n) → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (y : (X n)) :
    polynomialSphereRaising m (fun i => finitePolynomialField (fun a => b a i) c y) =
      finitePolynomialField (fun a => polynomialSphereRaising m (b a)) c y := by
  simp only [finitePolynomialField, smul_eq_C_mul]
  rw [polynomialSphereRaising_sum_family]
  simp_rw [polynomialSphereRaising_C_mul_family]

def raisedPolynomialField (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ) (y : (X n)) : MvPolynomial (I n) ℝ :=
  polynomialSphereRaising m (weightedFramePolynomialField g e b c f (m+1) 1 y)

def loweredPolynomialField (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ) (y : (X n)) : MvPolynomial (I n) ℝ :=
  polynomialDivergence (weightedFramePolynomialField g e b c f (m+1) (-1) y)

def fischerRaisingEnergy (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ) : ℝ :=
  ∫ y, metricDensity g y * normalizedFischerSquare (m+2) (raisedPolynomialField g e b c f m y)

def fischerLoweringEnergy (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ) : ℝ :=
  ∫ y, metricDensity g y * normalizedFischerSquare m (loweredPolynomialField g e b c f m y)

def raisingPolynomialFamily (m : ℕ) (b : ι → MvPolynomial (I n) ℝ) :
    (I n) × ((ι ⊕ ((I n) × (I n) × ι)) ⊕ ι) → MvPolynomial (I n) ℝ :=
  fun a => polynomialSphereRaising m (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a)

lemma raisedPolynomialField_eq_finite (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ) (y : (X n)) :
    raisedPolynomialField g e b c f m y = finitePolynomialField (raisingPolynomialFamily m b)
      (loweredWeightedTensorCoefficientFamily g e c f (m+1) 1) y := by
  unfold raisedPolynomialField raisingPolynomialFamily
  rw [← polynomialSphereRaising_finitePolynomialField]
  congr 1
  funext i
  exact (finitePolynomialField_weighted_indexed g e b c f (m+1) 1 y i).symm

lemma loweredPolynomialField_eq_trace (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ) (y : (X n)) :
    loweredPolynomialField g e b c f m y = loweredWeightedTraceField g e b c f (m+1) (-1) y :=
  polynomialDivergence_weightedFramePolynomialField g e b c f (m+1) (-1) y

lemma integrable_fischerRaisingEnergy {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Y) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (fun y => metricDensity g y * normalizedFischerSquare (m+2) (raisedPolynomialField g e b c f m y)) := by
  have hflat := weightedIndexed_flat_smooth_compact hY h hK e he c f (m+1) 1 hc hf hcompact hsupp
  have hh := integrable_weighted_fischerPair_local hY (metricDensity g) (h.contDiffOn_density hK)
    (raisingPolynomialFamily m b) (raisingPolynomialFamily m b) _ _
    hflat.1.contDiffOn hflat.1.contDiffOn hflat.2.1 (hflat.2.2.trans hsupp)
  simpa only [normalizedFischerSquare, normalizedFischerInner, Fintype.card_fin,
    raisedPolynomialField_eq_finite, loweredWeightedTensorCoefficientFamily, ← mul_div_assoc] using
    hh.div_const (sphereNormalization n (m+2))

lemma integrable_fischerLoweringEnergy {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Y) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (fun y => metricDensity g y * normalizedFischerSquare m (loweredPolynomialField g e b c f m y)) := by
  have hh := integrable_weightedTraceSquare hY h hK e he (metricDensity g) (h.contDiffOn_density hK)
    b c f (m+1) (-1) hc hf hcompact hsupp
  simpa only [normalizedFischerSquare, normalizedFischerInner, Fintype.card_fin,
    loweredPolynomialField_eq_trace, ← mul_div_assoc] using hh.div_const (sphereNormalization n m)

lemma weightedFramePolynomialField_harmonic {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, laplacian (b a) = 0) (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s : ℝ)
    {y : (X n)} (hy : y ∈ Y) (i : (I n)) : laplacian (weightedFramePolynomialField g e b c f k s y i) = 0 := by
  have hh := covariantPolynomialDerivative_harmonic g e b hb c y (e y i)
    (frameConnection_skew hY h hK e he hframe hy (e y i))
  have hadd (p q : MvPolynomial (I n) ℝ) : laplacian (p+q) = laplacian p + laplacian q := by
    simp [laplacian, map_add, Finset.sum_add_distrib]
  simp only [weightedFramePolynomialField, weightedPolynomialDerivative, hadd, laplacian_C_mul,
    hh, finitePolynomialField_harmonic b hb c y, mul_zero, add_zero]

def fischerFockNumerator (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (m : ℕ) (y : (X n)) : ℝ :=
  ((n:ℝ)+2*((m:ℝ)+1)) * (weightedFrameEnergy g e b c f (m+1) 1 y +
    (∑ i, ∑ j, fischerInner (loweredWeightedTensorField g e b c f (m+1) 1 y i j)
      (loweredWeightedTensorField g e b c f (m+1) 1 y j i)) -
    (4/(4*((m:ℝ)+(n:ℝ)/2)))*fischerInner (loweredWeightedTraceField g e b c f (m+1) 1 y)
      (loweredWeightedTraceField g e b c f (m+1) 1 y)) -
    ((n:ℝ)+2*(m:ℝ))*fischerInner (loweredWeightedTraceField g e b c f (m+1) (-1) y)
      (loweredWeightedTraceField g e b c f (m+1) (-1) y)

theorem raised_lowered_fock_difference_pointwise {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1))
    (hΔ : ∀ a, laplacian (b a) = 0)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (hsupp : tsupport c ⊆ Y) (y : (X n)) :
    normalizedFischerSquare (m+2) (raisedPolynomialField g e b c f m y) -
      normalizedFischerSquare m (loweredPolynomialField g e b c f m y) =
      fischerFockNumerator g e b c f m y / sphereNormalization n (m+1) := by
  by_cases hy : y ∈ Y
  · have hh := degree_fock_difference m
      (weightedFramePolynomialField g e b c f (m+1) 1 y)
      (weightedFramePolynomialField g e b c f (m+1) (-1) y)
      (fun i => by simpa only [weightedFramePolynomialField, Nat.cast_add, Nat.cast_one] using
        (weightedPolynomialDerivative_homogeneous (by omega) g e b hb c f 1 y (e y i)))
      (fun i => weightedFramePolynomialField_harmonic hY h hK e he hframe b hΔ c f (m+1) 1 hy i)
    simpa only [raisedPolynomialField, polynomialSphereRaising, loweredPolynomialField, fischerFockNumerator,
      polynomialDivergence_weightedFramePolynomialField, weightedFrameEnergy, weightedFramePolynomialField,
      loweredWeightedTensorField, weightedCovectorPolynomialDerivative_partial] using hh
  · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
    have hw : ∀ s : ℝ, weightedFramePolynomialField g e b c f (m+1) s y = 0 := by
      intro s
      funext i
      exact weightedPolynomialDerivative_zero_outside g e b c f (m+1) s hout (e y i)
    simp [raisedPolynomialField, loweredPolynomialField, fischerFockNumerator, hw,
      polynomialSphereRaising, harmonicRaising, polynomialRaising, polynomialDivergence,
      weightedFrameEnergy_zero_outside g e b c f (m+1) 1 hout,
      loweredWeightedTraceField_zero_outside g e b c f (m+1) 1 hout,
      loweredWeightedTraceField_zero_outside g e b c f (m+1) (-1) hout,
      loweredWeightedTensorField, weightedCovectorPolynomialDerivative_zero_outside g e _ c f (m+1) 1 hout,
      normalizedFischerSquare, normalizedFischerInner, fischerInner_zero_left]

end CalderonN
