module

public import Proof.CalderonN.FischerIntegralIdentities
import Mathlib.Tactic

@[expose] public section

/- Port of FischerIntegralBounds.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set MeasureTheory MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

theorem integratedFullCovectorCurvature_bound {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ y ∈ Ω, ∀ i j a b, |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ B)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (c : (X n) → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    |integratedFullCovectorCurvature g e b c| ≤
      (n : ℝ)^2*B*(k : ℝ)^2*(∫ y, metricDensity g y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
  have hE := integrable_fullCovectorCurvature hΩ h hK e he hframe b c (fun _ => 0) 0 hc contDiffOn_const hcompact hsupp
  have hU := integrable_weighted_fischerPair_local hΩ (metricDensity g) (h.contDiffOn_density hK)
    b b c c hc hc hcompact hsupp
  have hp (y : (X n)) : |metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y)| ≤
      ((n : ℝ)^2*B*(k : ℝ)^2)*(metricDensity g y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) := by
    by_cases hy : y ∈ Ω
    · have hρ : 0 ≤ metricDensity g y := Real.sqrt_nonneg _
      rw [abs_mul, abs_of_nonneg hρ]
      calc
        _ ≤ metricDensity g y * ((n : ℝ)^2*B*(k : ℝ)^2*fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) :=
          mul_le_mul_of_nonneg_left (fullCovectorCurvatureContraction_bound g e y B hB (hR y hy) hk _
            (finitePolynomialField_homogeneous b hb c y)) hρ
        _ = _ := by ring
    · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
      simp [finitePolynomialField_zero_outside b c hout, fullCovectorCurvatureContraction_zero, fischerInner_zero_left]
  calc
    _ ≤ ∫ y, |metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y, ((n : ℝ)^2*B*(k : ℝ)^2)*(metricDensity g y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) :=
      integral_mono hE.abs (hU.const_mul _) hp
    _ = _ := integral_const_mul _ _

lemma integrable_weightedFrameEnergy {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (ρ : (X n) → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (f : (X n) → ℝ) (hf : ContDiffOn ℝ ∞ f Ω)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) (k s : ℝ) :
    Integrable (fun y => ρ y * weightedFrameEnergy g e b c f k s y) := by
  obtain ⟨hD,hC,hM⟩ := integrable_frameEnergyTerms hΩ h hK e he ρ hρ f hf b c hc hcompact hsupp
  have hh := ((hD.const_mul (s^2)).add (hC.const_mul (s*k))).add (hM.const_mul (k^2))
  convert hh using 1
  funext y
  simp only [Pi.add_apply]
  rw [weightedFrameEnergy_expansion]
  ring

theorem loweredWeightedCrossEnergy_le {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (t : ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    loweredWeightedCrossEnergy g e b c f k t ≤
      (k : ℝ)*(∫ y, metricDensity g y * weightedFrameEnergy g e b c f k t y) := by
  have hρ := h.contDiffOn_density hK
  have hflat := weightedIndexed_flat_smooth_compact hΩ h hK e he c f k t hc hf hcompact hsupp
  have hA : Integrable (fun y => metricDensity g y * ∑ i, ∑ j,
      fischerInner (loweredWeightedTensorField g e b c f k t y i j) (loweredWeightedTensorField g e b c f k t y j i)) := by
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    simpa only [loweredWeightedTensorField_eq_finite, loweredWeightedTensorCoefficientFamily] using
      (integrable_weighted_fischerPair_local hΩ (metricDensity g) hρ
        (fun a => loweredWeightedTensorPolynomialFamily b a i j) (fun a => loweredWeightedTensorPolynomialFamily b a j i)
        _ _ hflat.1.contDiffOn hflat.1.contDiffOn hflat.2.1 (hflat.2.2.trans hsupp))
  have hW := integrable_weightedFrameEnergy hΩ h hK e he (metricDensity g) hρ f hf b c hc hcompact hsupp k t
  calc
    _ ≤ ∫ y, (k : ℝ)*(metricDensity g y * weightedFrameEnergy g e b c f k t y) := by
      apply integral_mono hA (hW.const_mul _)
      intro y
      have hp := mul_le_mul_of_nonneg_left (weightedLoweredCross_pointwise_le hk g e b hb c f t y)
        (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _)
      exact hp.trans_eq (by ring)
    _ = _ := integral_const_mul _ _

theorem loweredWeighted_second_integrated_inequality {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    loweredWeightedTraceSquare g e b c f k 1 ≤
      (k : ℝ)*(∫ y, metricDensity g y * weightedFrameEnergy g e b c f k (-1) y) -
      loweredHessianEnergy g e b c f k - integratedFullCovectorCurvature g e b c := by
  rw [loweredWeighted_second_integrated_identity hΩ h hK e he hframe b c f k hc hf hcompact hsupp]
  exact sub_le_sub_right (sub_le_sub_right (loweredWeightedCrossEnergy_le hΩ h hK e he hk b hb c f (-1) hc hf hcompact hsupp) _) _

end CalderonN
