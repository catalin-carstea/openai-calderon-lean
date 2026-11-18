import Proof.PolynomialDirectional
import Proof.GradientDivergence
import Proof.FischerAdjoint

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def weightedPolynomialDerivative (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) (y a : X) : MvPolynomial I ℝ :=
  C s * covariantPolynomialDerivative g e b c y a + C (k*fderiv ℝ f y a) * finitePolynomialField b c y

/-- The square expansion used in the supplied WeightedFischerSquare module. -/
lemma fischer_weighted_square (q p : MvPolynomial I ℝ) (s w : ℝ) :
    fischerInner (C s*q+C w*p) (C s*q+C w*p) =
      s^2*fischerInner q q + 2*s*w*fischerInner q p + w^2*fischerInner p p := by
  simp only [fischerInner_add_left, fischerInner_add_right, fischerInner_C_mul_left,
    fischerInner_C_mul_right, fischerInner_symm p q]
  ring

lemma weightedPolynomial_square_sum (g : MetricField) (e : Frame) (r : X → ℝ)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (k s : ℝ) (y : X)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    (∑ i, fischerInner (weightedPolynomialDerivative g e b c (fun x => Real.log (r x)) k s y (e y i))
      (weightedPolynomialDerivative g e b c (fun x => Real.log (r x)) k s y (e y i))) =
    s^2 * (∑ i, fischerInner (covariantPolynomialDerivative g e b c y (e y i))
      (covariantPolynomialDerivative g e b c y (e y i))) +
    2*s*k * (∑ i, fderiv ℝ (fun x => Real.log (r x)) y (e y i) *
      fischerInner (covariantPolynomialDerivative g e b c y (e y i)) (finitePolynomialField b c y)) +
    k^2 * (beta g r y)^2 * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y) := by
  simp only [weightedPolynomialDerivative, fischer_weighted_square]
  rw [beta_sq g e r y he]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma covariant_gradient_pairing (g : MetricField) (e : Frame) (f : X → ℝ)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (y : X) :
    fischerInner (covariantPolynomialDerivative g e b c y (metricGradient e f y)) (finitePolynomialField b c y) =
      ∑ i, fderiv ℝ f y (e y i) *
        fischerInner (covariantPolynomialDerivative g e b c y (e y i)) (finitePolynomialField b c y) := by
  rw [metricGradient, covariantPolynomialDerivative_direction_sum]
  simp only [fischerInner_sum_left, smul_eq_C_mul, fischerInner_C_mul_left]

/-- The cross term in the weighted square is minus the divergence of the metric gradient. -/
lemma compact_weighted_gradient_cross {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    (∫ y, metricDensity g y * 2 * (∑ i, fderiv ℝ f y (e y i) *
      fischerInner (covariantPolynomialDerivative g e b c y (e y i)) (finitePolynomialField b c y))) =
      -(∫ y, weightedDivergence (metricDensity g) (metricGradient e f) y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
  have hh := compact_local_covariant_fischer_contraction hΩ h hK e he hframe _
    (h.contDiffOn_density hK) (metricGradient e f) (contDiffOn_metricGradient hΩ e f he hf)
    b b c c hc hc hcompact hsupp
  have hpoint (y : X) : metricDensity g y *
      (fischerInner (covariantPolynomialDerivative g e b c y (metricGradient e f y)) (finitePolynomialField b c y) +
        fischerInner (finitePolynomialField b c y) (covariantPolynomialDerivative g e b c y (metricGradient e f y))) =
      metricDensity g y * 2 * (∑ i, fderiv ℝ f y (e y i) *
        fischerInner (covariantPolynomialDerivative g e b c y (e y i)) (finitePolynomialField b c y)) := by
    rw [fischerInner_symm (finitePolynomialField b c y), covariant_gradient_pairing]
    ring
  simpa only [hpoint] using hh

lemma profile_weighted_gradient_cross_nonneg {Y : Set X} (hY : IsOpen Y) {K : ℝ}
    {g : MetricField} (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ x ∈ Y, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    0 ≤ ∫ y, metricDensity g y * 2 * (∑ i, fderiv ℝ (fun x => Real.log (r x)) y (e y i) *
      fischerInner (covariantPolynomialDerivative g e b c y (e y i)) (finitePolynomialField b c y)) := by
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  rw [compact_weighted_gradient_cross hY h hK e he hframe _ hf b c hc hcompact hsupp]
  apply neg_nonneg.mpr
  apply integral_nonpos
  intro y
  by_cases hy : y ∈ Y
  · have hβ : 0 < beta g r y := (lt_of_lt_of_le zero_lt_one hfloor).trans_le (hp.2 y hy).2.1
    have hd := profile_gradient_divergence_bound hY h hK e he hframe hp hy
    have hneg : weightedDivergence (metricDensity g) (metricGradient e (fun x => Real.log (r x))) y ≤ 0 :=
      hd.trans (mul_nonpos_of_nonneg_of_nonpos (metricDensity_pos h hK hy).le (by nlinarith))
    exact mul_nonpos_of_nonpos_of_nonneg hneg (fischerInner_self_nonneg _)
  · have hout : y ∉ tsupport c := fun hx => hy (hsupp hx)
    have hc0 := image_eq_zero_of_notMem_tsupport hout
    simp [finitePolynomialField, hc0, fischerInner_zero_left]

end ShrinkingSpheres
