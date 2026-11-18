import Proof.ProfileFischerBounds
import Proof.ModelAlgebra

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def weightedFramePolynomialField (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) (y : X) (i : I) : MvPolynomial I ℝ :=
  weightedPolynomialDerivative g e b c f k s y (e y i)

lemma weightedFramePolynomialField_plus_eq (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k : ℕ) (y : X) :
    weightedFramePolynomialField g e b c f k 1 y =
      weightedDerivativePlus k (fun i => fderiv ℝ f y (e y i)) (finitePolynomialField b c y)
        (fun i => covariantPolynomialDerivative g e b c y (e y i)) := by
  funext i
  simp only [weightedFramePolynomialField, weightedPolynomialDerivative, weightedDerivativePlus,
    map_mul, map_one, one_mul, mul_assoc]

lemma weightedFramePolynomialField_minus_eq (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k : ℕ) (y : X) :
    weightedFramePolynomialField g e b c f k (-1) y =
      weightedDerivativeMinus k (fun i => fderiv ℝ f y (e y i)) (finitePolynomialField b c y)
        (fun i => covariantPolynomialDerivative g e b c y (e y i)) := by
  funext i
  simp only [weightedFramePolynomialField, weightedPolynomialDerivative, weightedDerivativeMinus,
    map_mul, map_neg, map_one, neg_one_mul, mul_assoc]

lemma polynomialDivergence_weightedFramePolynomialField (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) (y : X) :
    polynomialDivergence (weightedFramePolynomialField g e b c f k s y) =
      loweredWeightedTraceField g e b c f k s y := by
  simp only [polynomialDivergence, weightedFramePolynomialField, loweredWeightedTraceField,
    loweredWeightedTensorField, weightedCovectorPolynomialDerivative_partial]

lemma weightedFrameEnergy_zero_outside (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ)
    {y : X} (hy : y ∉ tsupport c) : weightedFrameEnergy g e b c f k s y = 0 := by
  simp [weightedFrameEnergy, weightedPolynomialDerivative_zero_outside g e b c f k s hy, fischerInner_zero_left]

lemma loweredWeightedTraceField_zero_outside (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ)
    {y : X} (hy : y ∉ tsupport c) : loweredWeightedTraceField g e b c f k s y = 0 := by
  simp [loweredWeightedTraceField, loweredWeightedTensorField,
    weightedCovectorPolynomialDerivative_zero_outside g e _ c f k s hy]

lemma integrable_weightedTraceSquare {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (ρ : X → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Y) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) (hc : ContDiff ℝ ∞ c)
    (hf : ContDiffOn ℝ ∞ f Y) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (fun y => ρ y * fischerInner (loweredWeightedTraceField g e b c f k s y)
      (loweredWeightedTraceField g e b c f k s y)) := by
  have hflat := weightedIndexed_flat_smooth_compact hY h hK e he c f k s hc hf hcompact hsupp
  simpa only [loweredWeightedTraceField_eq_finite, loweredWeightedTensorCoefficientFamily] using
    (integrable_weighted_fischerPair_local hY ρ hρ (weightedTracePolynomialFamily b) (weightedTracePolynomialFamily b)
      _ _ hflat.1.contDiffOn hflat.1.contDiffOn hflat.2.1 (hflat.2.2.trans hsupp))

lemma Profile.contDiffOn_beta_inv {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) {e : Frame} {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ}
    (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor) :
    ContDiffOn ℝ ∞ (fun y => (beta g r y)⁻¹) Y :=
  (hp.contDiffOn_beta hY h hK hfloor).inv (fun y hy =>
    ((lt_of_lt_of_le zero_lt_one hfloor).trans_le (hp.2 y hy).2.1).ne')

def profileWeightedFrameEnergy (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (r : X → ℝ) (k s : ℝ) : ℝ :=
  ∫ y, metricDensity g y * (beta g r y)⁻¹ * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k s y

def profileWeightedTraceSquare (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (r : X → ℝ) (k s : ℝ) : ℝ :=
  ∫ y, metricDensity g y * (beta g r y)⁻¹ *
    fischerInner (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k s y)
      (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k s y)

def profileFischerMass (g : MetricField) (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (r : X → ℝ) : ℝ :=
  ∫ y, metricDensity g y * beta g r y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)

lemma profileTrace_convex_bound_global {Y : Set X} {g : MetricField} {e : Frame} {r : X → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (c : X → ι → ℝ) (hsupp : tsupport c ⊆ Y) (a : ℝ) (ha : 0 ≤ a) (haf : a ≤ floor) (y : X) :
    fischerInner (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k 1 y)
      (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k 1 y) ≤
      ((k : ℝ)+2) * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y -
      a*((k : ℝ)+2)*(beta g r y)⁻¹ * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y +
      2*a*(beta g r y)⁻¹ * fischerInner (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k (-1) y)
        (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k (-1) y) +
      8*a*(k : ℝ)^3*beta g r y*fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y) := by
  by_cases hy : y ∈ Y
  · have hβ : 0 < beta g r y := (lt_of_lt_of_le zero_lt_one hfloor).trans_le (hp.2 y hy).2.1
    have hh := profile_divergence_convex_bound g e r y (hframe y hy) hk (finitePolynomialField b c y)
      (fun i => covariantPolynomialDerivative g e b c y (e y i)) (finitePolynomialField_homogeneous b hb c y)
      (fun i => covariantPolynomialDerivative_homogeneous hk g e b hb c y (e y i)) a ha
      (haf.trans (hp.2 y hy).2.1) hβ
    have hgrad : profileGradient r e y = (fun i => fderiv ℝ (fun x => Real.log (r x)) y (e y i)) := rfl
    rw [hgrad] at hh
    simp_rw [← weightedFramePolynomialField_plus_eq g e b c (fun x => Real.log (r x)) k y,
      ← weightedFramePolynomialField_minus_eq g e b c (fun x => Real.log (r x)) k y,
      polynomialDivergence_weightedFramePolynomialField] at hh
    change _ ≤ (1-a/beta g r y)*(((k : ℝ)+2)*weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y) + _ at hh
    convert hh using 1
    field_simp [hβ.ne']
    ring
  · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
    simp [loweredWeightedTraceField_zero_outside g e b c _ _ _ hout,
      weightedFrameEnergy_zero_outside g e b c _ _ _ hout, finitePolynomialField_zero_outside b c hout, fischerInner_zero_left]

lemma Profile.integrable_inv_frameEnergy {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (k s : ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (fun y => metricDensity g y * (beta g r y)⁻¹ *
      weightedFrameEnergy g e b c (fun x => Real.log (r x)) k s y) :=
  integrable_weightedFrameEnergy hY h hK e he _
    ((h.contDiffOn_density hK).mul (hp.contDiffOn_beta_inv hY h hK hfloor)) _
    (hp.1.log (fun x hx => (hp.2 x hx).1.ne')) b c hc hcompact hsupp k s

lemma Profile.integrable_inv_traceSquare {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (k s : ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (fun y => metricDensity g y * (beta g r y)⁻¹ *
      fischerInner (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k s y)
        (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k s y)) :=
  integrable_weightedTraceSquare hY h hK e he _
    ((h.contDiffOn_density hK).mul (hp.contDiffOn_beta_inv hY h hK hfloor)) b c _ k s hc
    (hp.1.log (fun x hx => (hp.2 x hx).1.ne')) hcompact hsupp

lemma profileWeightedFrameEnergy_nonneg (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (r : X → ℝ) (k s : ℝ) : 0 ≤ profileWeightedFrameEnergy g e b c r k s := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (Finset.sum_nonneg (fun i _ => fischerInner_self_nonneg _))

lemma profileWeightedTraceSquare_nonneg (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (r : X → ℝ) (k s : ℝ) : 0 ≤ profileWeightedTraceSquare g e b c r k s := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (fischerInner_self_nonneg _)

lemma Profile.weightedTraceSquare_le {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (k s : ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    profileWeightedTraceSquare g e b c r k s ≤
      floor⁻¹ * loweredWeightedTraceSquare g e b c (fun x => Real.log (r x)) k s := by
  have hZ := hp.integrable_inv_traceSquare hY h hK e he hfloor b c k s hc hcompact hsupp
  have hS := integrable_weightedTraceSquare hY h hK e he (metricDensity g) (h.contDiffOn_density hK)
    b c _ k s hc (hp.1.log (fun x hx => (hp.2 x hx).1.ne')) hcompact hsupp
  calc
    _ ≤ ∫ y, floor⁻¹ * (metricDensity g y * fischerInner
        (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k s y)
        (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k s y)) := by
      apply integral_mono hZ (hS.const_mul _)
      intro y
      by_cases hy : y ∈ Y
      · have hi : (beta g r y)⁻¹ ≤ floor⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hfloor) (hp.2 y hy).2.1
        have hh := mul_le_mul_of_nonneg_right hi (mul_nonneg (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _)
          (fischerInner_self_nonneg (loweredWeightedTraceField g e b c (fun x => Real.log (r x)) k s y)))
        convert hh using 1 <;> ring
      · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
        simp [loweredWeightedTraceField_zero_outside g e b c _ _ _ hout, fischerInner_zero_left]
    _ = _ := integral_const_mul _ _

theorem Profile.trace_convex_integrated_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ j, (b j).IsHomogeneous k)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    (a : ℝ) (ha : 0 ≤ a) (haf : a ≤ floor) :
    loweredWeightedTraceSquare g e b c (fun x => Real.log (r x)) k 1 ≤
      ((k : ℝ)+2)*(∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y) -
      a*((k : ℝ)+2)*profileWeightedFrameEnergy g e b c r k 1 +
      2*a*profileWeightedTraceSquare g e b c r k (-1) + 8*a*(k : ℝ)^3*profileFischerMass g b c r := by
  let f := fun x => Real.log (r x)
  let X := fun y => metricDensity g y * weightedFrameEnergy g e b c f k 1 y
  let W := fun y => metricDensity g y * (beta g r y)⁻¹ * weightedFrameEnergy g e b c f k 1 y
  let Z := fun y => metricDensity g y * (beta g r y)⁻¹ * fischerInner
    (loweredWeightedTraceField g e b c f k (-1) y) (loweredWeightedTraceField g e b c f k (-1) y)
  let M := fun y => metricDensity g y * beta g r y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)
  have hf : ContDiffOn ℝ ∞ f Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hX : Integrable X := integrable_weightedFrameEnergy hY h hK e he (metricDensity g) (h.contDiffOn_density hK)
    f hf b c hc hcompact hsupp k 1
  have hW : Integrable W := hp.integrable_inv_frameEnergy hY h hK e he hfloor b c k 1 hc hcompact hsupp
  have hZ : Integrable Z := hp.integrable_inv_traceSquare hY h hK e he hfloor b c k (-1) hc hcompact hsupp
  have hM : Integrable M := hp.integrable_beta_fischer hY h hK hfloor b c hc.contDiffOn hcompact hsupp
  have hS := integrable_weightedTraceSquare hY h hK e he (metricDensity g) (h.contDiffOn_density hK)
    b c f k 1 hc hf hcompact hsupp
  let A := fun y => ((k : ℝ)+2)*X y
  let B := fun y => a*((k : ℝ)+2)*W y
  let Cc := fun y => 2*a*Z y
  let Dd := fun y => 8*a*(k : ℝ)^3*M y
  have hA : Integrable A := hX.const_mul _
  have hB : Integrable B := hW.const_mul _
  have hCc : Integrable Cc := hZ.const_mul _
  have hDd : Integrable Dd := hM.const_mul _
  calc
    _ ≤ ∫ y, ((A-B)+Cc) y + Dd y := by
      apply integral_mono hS (((hA.sub hB).add hCc).add hDd)
      intro y
      have hh := mul_le_mul_of_nonneg_left
        (profileTrace_convex_bound_global hp hfloor hframe hk b hb c hsupp a ha haf y)
        (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _)
      apply hh.trans_eq
      dsimp only [A, B, Cc, Dd, X, W, Z, M, f, Pi.add_apply, Pi.sub_apply]
      ring
    _ = _ := by
      rw [integral_add ((hA.sub hB).add hCc) hDd]
      change (∫ y, (A-B) y + Cc y) + (∫ y, Dd y) = _
      rw [integral_add (hA.sub hB) hCc]
      change (∫ y, A y - B y) + (∫ y, Cc y) + (∫ y, Dd y) = _
      rw [integral_sub hA hB]
      simp only [A, B, Cc, Dd, integral_const_mul]
      rfl

theorem Profile.trace_convex_uniform_integrated_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ j, (b j).IsHomogeneous k)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    (a : ℝ) (ha : 0 ≤ a) (haf : a ≤ floor) :
    loweredWeightedTraceSquare g e b c (fun x => Real.log (r x)) k 1 ≤
      ((k : ℝ)+2)*(∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y) -
      a*((k : ℝ)+2)*profileWeightedFrameEnergy g e b c r k 1 +
      (2*a/floor)*loweredWeightedTraceSquare g e b c (fun x => Real.log (r x)) k (-1) +
      8*a*(k : ℝ)^3*profileFischerMass g b c r := by
  have h1 := hp.trace_convex_integrated_bound hY h hK e he hframe hfloor hk b hb c hc hcompact hsupp a ha haf
  have h2 := mul_le_mul_of_nonneg_left (hp.weightedTraceSquare_le hY h hK e he hfloor b c k (-1) hc hcompact hsupp)
    (show 0 ≤ 2*a by positivity)
  have h2' : 2*a*profileWeightedTraceSquare g e b c r k (-1) ≤
      (2*a/floor)*loweredWeightedTraceSquare g e b c (fun x => Real.log (r x)) k (-1) := by
    simpa only [div_eq_mul_inv, mul_assoc] using h2
  linarith only [h1, h2']

end ShrinkingSpheres
