import Proof.WeightedPolynomial

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def covariantFrameEnergy (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (y : X) : ℝ :=
  ∑ i, fischerInner (covariantPolynomialDerivative g e b c y (e y i))
    (covariantPolynomialDerivative g e b c y (e y i))

def weightedFrameEnergy (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) (y : X) : ℝ :=
  ∑ i, fischerInner (weightedPolynomialDerivative g e b c f k s y (e y i))
    (weightedPolynomialDerivative g e b c f k s y (e y i))

def frameGradientSq (e : Frame) (f : X → ℝ) (y : X) : ℝ :=
  ∑ i, (fderiv ℝ f y (e y i))^2

def polynomialGradientCross (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (y : X) : ℝ :=
  2 * ∑ i, fderiv ℝ f y (e y i) *
    fischerInner (covariantPolynomialDerivative g e b c y (e y i)) (finitePolynomialField b c y)

lemma weightedFrameEnergy_expansion (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) (y : X) :
    weightedFrameEnergy g e b c f k s y = s^2 * covariantFrameEnergy g e b c y +
      s*k * polynomialGradientCross g e b c f y +
      k^2 * frameGradientSq e f y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y) := by
  simp only [weightedFrameEnergy, weightedPolynomialDerivative, fischer_weighted_square,
    covariantFrameEnergy, polynomialGradientCross, frameGradientSq,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma integrable_frameEnergyTerms {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (ρ : X → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Ω)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    Integrable (fun y => ρ y * covariantFrameEnergy g e b c y) ∧
    Integrable (fun y => ρ y * polynomialGradientCross g e b c f y) ∧
    Integrable (fun y => ρ y * frameGradientSq e f y *
      fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
  have hdc (i : I) := derivativeCoefficientFamily_smooth_compact hΩ h hK e he c
    (fun x => e x i) hc (he i) hcompact hsupp
  have hfi (i : I) : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (e y i)) Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply (he i)
  have hD (i : I) : Integrable (fun y => ρ y *
      fischerInner (covariantPolynomialDerivative g e b c y (e y i))
        (covariantPolynomialDerivative g e b c y (e y i))) := by
    simpa only [← covariantPolynomialDerivative_eq_augmented] using
      integrable_weighted_fischerPair_local hΩ ρ hρ (derivativePolynomialFamily b)
        (derivativePolynomialFamily b) _ _ (hdc i).1.contDiffOn (hdc i).1.contDiffOn
        (hdc i).2.1 ((hdc i).2.2.trans hsupp)
  have hC (i : I) : Integrable (fun y => ρ y * 2 * (fderiv ℝ f y (e y i) *
      fischerInner (covariantPolynomialDerivative g e b c y (e y i)) (finitePolynomialField b c y))) := by
    have hh := integrable_weighted_fischerPair_local hΩ (fun y => ρ y * 2 * fderiv ℝ f y (e y i))
      ((hρ.mul contDiffOn_const).mul (hfi i)) (derivativePolynomialFamily b) b _ c
      (hdc i).1.contDiffOn hc.contDiffOn (hdc i).2.1 ((hdc i).2.2.trans hsupp)
    simpa only [← covariantPolynomialDerivative_eq_augmented, mul_assoc] using hh
  refine ⟨?_, ?_, ?_⟩
  · simpa only [covariantFrameEnergy, Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun i _ => hD i)
  · simpa only [polynomialGradientCross, ← mul_assoc, Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun i _ => hC i)
  · exact integrable_weighted_fischerPair_local hΩ _
      (hρ.mul (ContDiffOn.sum (fun i _ => (hfi i).pow 2))) b b c c
      hc.contDiffOn hc.contDiffOn hcompact hsupp

lemma compact_weighted_energy_expansion {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (ρ : X → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Ω)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) (k s : ℝ) :
    (∫ y, ρ y * weightedFrameEnergy g e b c f k s y) =
      s^2 * (∫ y, ρ y * covariantFrameEnergy g e b c y) +
      s*k * (∫ y, ρ y * polynomialGradientCross g e b c f y) +
      k^2 * (∫ y, ρ y * frameGradientSq e f y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
  obtain ⟨hD,hC,hM⟩ := integrable_frameEnergyTerms hΩ h hK e he ρ hρ f hf b c hc hcompact hsupp
  have hpoint (y : X) : ρ y * weightedFrameEnergy g e b c f k s y =
      s^2 * (ρ y * covariantFrameEnergy g e b c y) +
      s*k * (ρ y * polynomialGradientCross g e b c f y) +
      k^2 * (ρ y * frameGradientSq e f y *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
    rw [weightedFrameEnergy_expansion]
    ring
  simp_rw [hpoint]
  have hsplit := integral_add ((hD.const_mul (s^2)).add (hC.const_mul (s*k))) (hM.const_mul (k^2))
  have hsplit' := integral_add (hD.const_mul (s^2)) (hC.const_mul (s*k))
  simp only [Pi.add_apply] at hsplit hsplit'
  rw [hsplit, hsplit', integral_const_mul, integral_const_mul, integral_const_mul]

/-- For a concave admissible log-radius, the weighted derivative energy controls both its
    unweighted derivative part and its degree-squared radial mass. -/
theorem profile_weighted_energy_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ}
    {g : MetricField} (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ x ∈ Y, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hsupp : tsupport c ⊆ Y) {k : ℝ} (hk : 0 ≤ k) :
    (∫ y, metricDensity g y * covariantFrameEnergy g e b c y) +
      k^2 * (∫ y, metricDensity g y * (beta g r y)^2 *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) ≤
    (∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y) := by
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hmass : (fun y => metricDensity g y * frameGradientSq e (fun x => Real.log (r x)) y *
      fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) =
      (fun y => metricDensity g y * (beta g r y)^2 *
        fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
    funext y
    by_cases hy : y ∈ Y
    · rw [beta_sq g e r y (hframe y hy)]
      rfl
    · have hc0 := image_eq_zero_of_notMem_tsupport (fun ht => hy (hsupp ht))
      simp [finitePolynomialField, hc0, fischerInner_zero_left]
  have hcross := profile_weighted_gradient_cross_nonneg hY h hK e he hframe hp hc₀ hfloor b c hc hcompact hsupp
  have hcross' : 0 ≤ ∫ y, metricDensity g y * polynomialGradientCross g e b c (fun x => Real.log (r x)) y := by
    simpa only [polynomialGradientCross, ← mul_assoc] using hcross
  rw [compact_weighted_energy_expansion hY h hK e he _ (h.contDiffOn_density hK) _ hf b c hc hcompact hsupp,
    hmass]
  simp only [one_pow, one_mul]
  nlinarith [mul_nonneg hk hcross']

end ShrinkingSpheres
