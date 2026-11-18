import Proof.ProfileConvexity

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

def polynomialSphereRaising (m : ℕ) (q : I → MvPolynomial I ℝ) : MvPolynomial I ℝ :=
  C (2*(m : ℝ)+5) * harmonicRaising m q

lemma polynomialSphereRaising_sum_family {J : Type*} [Fintype J] (m : ℕ) (q : J → I → MvPolynomial I ℝ) :
    polynomialSphereRaising m (fun i => ∑ a, q a i) = ∑ a, polynomialSphereRaising m (q a) := by
  simp only [polynomialSphereRaising, harmonicRaising, polynomialRaising, polynomialDivergence,
    Fin.sum_univ_three, map_sum]
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma polynomialSphereRaising_C_mul_family (m : ℕ) (q : I → MvPolynomial I ℝ) (a : ℝ) :
    polynomialSphereRaising m (fun i => C a * q i) = C a * polynomialSphereRaising m q := by
  simp only [polynomialSphereRaising, harmonicRaising, polynomialRaising, polynomialDivergence,
    Fin.sum_univ_three, pderiv_C_mul]
  ring

variable {ι : Type*} [Fintype ι]

lemma polynomialSphereRaising_finitePolynomialField (m : ℕ) (b : ι → I → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (y : X) :
    polynomialSphereRaising m (fun i => finitePolynomialField (fun a => b a i) c y) =
      finitePolynomialField (fun a => polynomialSphereRaising m (b a)) c y := by
  simp only [finitePolynomialField, smul_eq_C_mul]
  rw [polynomialSphereRaising_sum_family]
  simp_rw [polynomialSphereRaising_C_mul_family]

def raisedPolynomialField (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) (y : X) : MvPolynomial I ℝ :=
  polynomialSphereRaising m (weightedFramePolynomialField g e b c f (m+1) 1 y)

def loweredPolynomialField (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) (y : X) : MvPolynomial I ℝ :=
  polynomialDivergence (weightedFramePolynomialField g e b c f (m+1) (-1) y)

def fischerRaisingEnergy (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) : ℝ :=
  ∫ y, metricDensity g y * normalizedFischerSquare (m+2) (raisedPolynomialField g e b c f m y)

def fischerLoweringEnergy (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) : ℝ :=
  ∫ y, metricDensity g y * normalizedFischerSquare m (loweredPolynomialField g e b c f m y)

def raisingPolynomialFamily (m : ℕ) (b : ι → MvPolynomial I ℝ) :
    I × ((ι ⊕ (I × I × ι)) ⊕ ι) → MvPolynomial I ℝ :=
  fun a => polynomialSphereRaising m (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a)

lemma raisedPolynomialField_eq_finite (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) (y : X) :
    raisedPolynomialField g e b c f m y = finitePolynomialField (raisingPolynomialFamily m b)
      (loweredWeightedTensorCoefficientFamily g e c f (m+1) 1) y := by
  unfold raisedPolynomialField raisingPolynomialFamily
  rw [← polynomialSphereRaising_finitePolynomialField]
  congr 1
  funext i
  exact (finitePolynomialField_weighted_indexed g e b c f (m+1) 1 y i).symm

lemma loweredPolynomialField_eq_trace (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) (y : X) :
    loweredPolynomialField g e b c f m y = loweredWeightedTraceField g e b c f (m+1) (-1) y :=
  polynomialDivergence_weightedFramePolynomialField g e b c f (m+1) (-1) y

lemma integrable_fischerRaisingEnergy {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Y) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (fun y => metricDensity g y * normalizedFischerSquare (m+2) (raisedPolynomialField g e b c f m y)) := by
  have hflat := weightedIndexed_flat_smooth_compact hY h hK e he c f (m+1) 1 hc hf hcompact hsupp
  have hh := integrable_weighted_fischerPair_local hY (metricDensity g) (h.contDiffOn_density hK)
    (raisingPolynomialFamily m b) (raisingPolynomialFamily m b) _ _
    hflat.1.contDiffOn hflat.1.contDiffOn hflat.2.1 (hflat.2.2.trans hsupp)
  simpa only [normalizedFischerSquare, normalizedFischerInner, Fintype.card_fin,
    raisedPolynomialField_eq_finite, loweredWeightedTensorCoefficientFamily, ← mul_div_assoc] using
    hh.div_const (sphereNormalization 3 (m+2))

lemma integrable_fischerLoweringEnergy {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Y) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (fun y => metricDensity g y * normalizedFischerSquare m (loweredPolynomialField g e b c f m y)) := by
  have hh := integrable_weightedTraceSquare hY h hK e he (metricDensity g) (h.contDiffOn_density hK)
    b c f (m+1) (-1) hc hf hcompact hsupp
  simpa only [normalizedFischerSquare, normalizedFischerInner, Fintype.card_fin,
    loweredPolynomialField_eq_trace, ← mul_div_assoc] using hh.div_const (sphereNormalization 3 m)

lemma weightedFramePolynomialField_harmonic {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (hb : ∀ a, laplacian (b a) = 0) (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ)
    {y : X} (hy : y ∈ Y) (i : I) : laplacian (weightedFramePolynomialField g e b c f k s y i) = 0 := by
  have hh := covariantPolynomialDerivative_harmonic g e b hb c y (e y i)
    (frameConnection_skew hY h hK e he hframe hy (e y i))
  have hadd (p q : MvPolynomial I ℝ) : laplacian (p+q) = laplacian p + laplacian q := by
    simp [laplacian, map_add, Finset.sum_add_distrib]
  simp only [weightedFramePolynomialField, weightedPolynomialDerivative, hadd, laplacian_C_mul,
    hh, finitePolynomialField_harmonic b hb c y, mul_zero, add_zero]

def fischerFockNumerator (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (m : ℕ) (y : X) : ℝ :=
  (2*(m : ℝ)+5) * (weightedFrameEnergy g e b c f (m+1) 1 y +
    (∑ i, ∑ j, fischerInner (loweredWeightedTensorField g e b c f (m+1) 1 y i j)
      (loweredWeightedTensorField g e b c f (m+1) 1 y j i)) -
    (4/(4*(m : ℝ)+6))*fischerInner (loweredWeightedTraceField g e b c f (m+1) 1 y)
      (loweredWeightedTraceField g e b c f (m+1) 1 y)) -
    (2*(m : ℝ)+3)*fischerInner (loweredWeightedTraceField g e b c f (m+1) (-1) y)
      (loweredWeightedTraceField g e b c f (m+1) (-1) y)

theorem raised_lowered_fock_difference_pointwise {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1))
    (hΔ : ∀ a, laplacian (b a) = 0)
    (c : X → ι → ℝ) (f : X → ℝ) (hsupp : tsupport c ⊆ Y) (y : X) :
    normalizedFischerSquare (m+2) (raisedPolynomialField g e b c f m y) -
      normalizedFischerSquare m (loweredPolynomialField g e b c f m y) =
      fischerFockNumerator g e b c f m y / sphereNormalization 3 (m+1) := by
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

end ShrinkingSpheres
