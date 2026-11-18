import Proof.FiniteFockEnergy

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

lemma integrable_loweredWeightedTensor_pair {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Y) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    (i j a l : I) : Integrable (fun y => metricDensity g y *
      fischerInner (loweredWeightedTensorField g e b c f k s y i j) (loweredWeightedTensorField g e b c f k t y a l)) := by
  have hs := weightedIndexed_flat_smooth_compact hY h hK e he c f k s hc hf hcompact hsupp
  have ht := weightedIndexed_flat_smooth_compact hY h hK e he c f k t hc hf hcompact hsupp
  simpa only [loweredWeightedTensorField_eq_finite, loweredWeightedTensorCoefficientFamily] using
    (integrable_weighted_fischerPair_local hY (metricDensity g) (h.contDiffOn_density hK)
      (fun q => loweredWeightedTensorPolynomialFamily b q i j) (fun q => loweredWeightedTensorPolynomialFamily b q a l)
      _ _ hs.1.contDiffOn ht.1.contDiffOn hs.2.1 (hs.2.2.trans hsupp))

theorem fischerRaisingEnergy_sub_loweringEnergy_integral {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1)) (hΔ : ∀ a, laplacian (b a) = 0)
    (c : X → ι → ℝ) (f : X → ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Y)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    fischerRaisingEnergy g e b c f m - fischerLoweringEnergy g e b c f m =
      (∫ y, metricDensity g y * fischerFockNumerator g e b c f m y) / sphereNormalization 3 (m+1) := by
  rw [fischerRaisingEnergy, fischerLoweringEnergy,
    ← integral_sub (integrable_fischerRaisingEnergy hY h hK e he b c f m hc hf hcompact hsupp)
      (integrable_fischerLoweringEnergy hY h hK e he b c f m hc hf hcompact hsupp)]
  have heq : (fun y => metricDensity g y * normalizedFischerSquare (m+2) (raisedPolynomialField g e b c f m y) -
      metricDensity g y * normalizedFischerSquare m (loweredPolynomialField g e b c f m y)) =
      fun y => (metricDensity g y * fischerFockNumerator g e b c f m y) / sphereNormalization 3 (m+1) := by
    funext y
    rw [← mul_sub, raised_lowered_fock_difference_pointwise hY h hK e he hframe m b hb hΔ c f hsupp y]
    ring
  rw [heq, integral_div]

theorem integral_fischerFockNumerator {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Y) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    (∫ y, metricDensity g y * fischerFockNumerator g e b c f m y) =
      (2*(m : ℝ)+5)*((∫ y, metricDensity g y * weightedFrameEnergy g e b c f (m+1) 1 y) +
        loweredWeightedCrossEnergy g e b c f (m+1) 1 -
        (4/(4*(m : ℝ)+6))*loweredWeightedTraceSquare g e b c f (m+1) 1) -
      (2*(m : ℝ)+3)*loweredWeightedTraceSquare g e b c f (m+1) (-1) := by
  let X := fun y => metricDensity g y * weightedFrameEnergy g e b c f (m+1) 1 y
  let Cc := fun y => metricDensity g y * ∑ i, ∑ j,
    fischerInner (loweredWeightedTensorField g e b c f (m+1) 1 y i j) (loweredWeightedTensorField g e b c f (m+1) 1 y j i)
  let Sp := fun y => metricDensity g y * fischerInner (loweredWeightedTraceField g e b c f (m+1) 1 y)
    (loweredWeightedTraceField g e b c f (m+1) 1 y)
  let Sm := fun y => metricDensity g y * fischerInner (loweredWeightedTraceField g e b c f (m+1) (-1) y)
    (loweredWeightedTraceField g e b c f (m+1) (-1) y)
  have hρ := h.contDiffOn_density hK
  have hX : Integrable X := integrable_weightedFrameEnergy hY h hK e he (metricDensity g) hρ f hf b c hc hcompact hsupp (m+1) 1
  have hC : Integrable Cc := by
    simp only [Cc, Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_loweredWeightedTensor_pair hY h hK e he b c f (m+1) 1 1 hc hf hcompact hsupp i j j i))
  have hSp : Integrable Sp := integrable_weightedTraceSquare hY h hK e he (metricDensity g) hρ b c f (m+1) 1 hc hf hcompact hsupp
  have hSm : Integrable Sm := integrable_weightedTraceSquare hY h hK e he (metricDensity g) hρ b c f (m+1) (-1) hc hf hcompact hsupp
  let XS := fun y => (X+Cc) y - (4/(4*(m : ℝ)+6))*Sp y
  have hXS : Integrable XS := (hX.add hC).sub (hSp.const_mul _)
  have hiXS : (∫ y, XS y) = (∫ y, X y) + (∫ y, Cc y) - (4/(4*(m : ℝ)+6))*(∫ y, Sp y) := by
    change (∫ y, (X+Cc) y - (4/(4*(m : ℝ)+6))*Sp y) = _
    rw [integral_sub (hX.add hC) (hSp.const_mul _)]
    change (∫ y, X y + Cc y) - (∫ y, (4/(4*(m : ℝ)+6))*Sp y) = _
    rw [integral_add hX hC, integral_const_mul]
  have hp : (fun y => metricDensity g y * fischerFockNumerator g e b c f m y) =
      fun y => (2*(m : ℝ)+5)*XS y - (2*(m : ℝ)+3)*Sm y := by
    funext y
    simp only [fischerFockNumerator, XS, Pi.add_apply, X, Cc, Sp, Sm]
    ring
  rw [hp, integral_sub (hXS.const_mul _) (hSm.const_mul _), integral_const_mul, integral_const_mul, hiXS]
  rfl

theorem fischerRaisingEnergy_sub_loweringEnergy_reduced {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (m : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ a, (b a).IsHomogeneous (m+1)) (hΔ : ∀ a, laplacian (b a) = 0)
    (c : X → ι → ℝ) (f : X → ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Y)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    fischerRaisingEnergy g e b c f m - fischerLoweringEnergy g e b c f m =
      ((2*(m : ℝ)+5)*((∫ y, metricDensity g y * weightedFrameEnergy g e b c f (m+1) 1 y) -
        (4/(4*(m : ℝ)+6))*loweredWeightedTraceSquare g e b c f (m+1) 1 -
        loweredHessianEnergy g e b c f (m+1)) +
      2*loweredWeightedTraceSquare g e b c f (m+1) (-1) +
      (2*(m : ℝ)+5)*integratedFullCovectorCurvature g e b c) / sphereNormalization 3 (m+1) := by
  rw [fischerRaisingEnergy_sub_loweringEnergy_integral hY h hK e he hframe m b hb hΔ c f hc hf hcompact hsupp,
    integral_fischerFockNumerator hY h hK e he m b c f hc hf hcompact hsupp,
    loweredWeighted_first_integrated_identity hY h hK e he hframe b c f (m+1) hc hf hcompact hsupp]
  ring

end ShrinkingSpheres
