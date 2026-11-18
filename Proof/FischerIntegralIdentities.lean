import Proof.FischerMixedIdentities

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def fischerMixedCross (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ) (y : X) : ℝ :=
  ∑ i, ∑ j, fischerInner (pderiv j (finitePolynomialField b c y))
    (loweredWeightedSecondTensorField g e b c f k s t y i j i)

def fischerMixedTrace (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ) (y : X) : ℝ :=
  ∑ j, ∑ i, fischerInner (pderiv j (finitePolynomialField b c y))
    (loweredWeightedSecondTensorField g e b c f k s t y j i i)

def fischerHessianForm (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ) (y : X) : ℝ :=
  ∑ i, ∑ j, (2*k*hessianBilinear g f y (e y i) (e y j)) *
    fischerInner (pderiv i (finitePolynomialField b c y)) (pderiv j (finitePolynomialField b c y))

def loweredHessianEnergy (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ) : ℝ := ∫ y, metricDensity g y * fischerHessianForm g e b c f k y

def integratedFullCovectorCurvature (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) : ℝ := ∫ y, metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y)

lemma integrable_loweredSecond_pair {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω)
    (a i j l : I) : Integrable (fun y => metricDensity g y * fischerInner (pderiv a (finitePolynomialField b c y))
      (loweredWeightedSecondTensorField g e b c f k s t y i j l)) := by
  have hz := weightedIndexed_flat_smoothOn hΩ h hK e he c f k t hc hf
  have hreg := contDiffOn_weightedTensor_fischer_right hΩ h hK e he _ (he i)
    (fun q => pderiv a (b q)) (loweredWeightedTensorPolynomialFamily b) c
    (loweredWeightedTensorCoefficientFamily g e c f k t) f k s hc hz hf j l
  apply integrable_local_supported hΩ c hcompact hsupp _
    ((h.contDiffOn_density hK).mul (by
      simpa only [finitePolynomialField_partial, loweredWeightedSecondTensorField] using hreg))
  intro y hy
  simp [finitePolynomialField_zero_outside b c hy, fischerInner_zero_left]

lemma integrable_fischerMixedCross {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    Integrable (fun y => metricDensity g y * fischerMixedCross g e b c f k s t y) := by
  simp only [fischerMixedCross, Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_loweredSecond_pair hΩ h hK e he b c f k s t hc hf hcompact hsupp j i j i))

lemma integrable_fischerMixedTrace {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    Integrable (fun y => metricDensity g y * fischerMixedTrace g e b c f k s t y) := by
  simp only [fischerMixedTrace, Finset.mul_sum]
  exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ =>
    integrable_loweredSecond_pair hΩ h hK e he b c f k s t hc hf hcompact hsupp j j i i))

lemma integrable_fischerHessianForm {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    Integrable (fun y => metricDensity g y * fischerHessianForm g e b c f k y) := by
  have hdf := hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)
  have hddf := hdf.fderiv_of_isOpen (m := ∞) hΩ (by simp)
  have hH (i j : I) : ContDiffOn ℝ ∞ (fun y => hessianBilinear g f y (e y i) (e y j)) Ω := by
    simp only [hessianBilinear_apply]
    exact ((hddf.clm_apply (he i)).clm_apply (he j)).sub
      (hdf.clm_apply (h.contDiffOn_connection hΩ hK _ _ (he i) (he j)))
  have hPair (i j : I) : ContDiffOn ℝ ∞ (fun y => fischerInner (pderiv i (finitePolynomialField b c y))
      (pderiv j (finitePolynomialField b c y))) Ω := by
    simpa only [finitePolynomialField_partial] using
      (contDiffOn_fischerPair (fun a => pderiv i (b a)) (fun a => pderiv j (b a)) c c hc hc)
  have hform : ContDiffOn ℝ ∞ (fischerHessianForm g e b c f k) Ω :=
    ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => 2*k) Ω).mul (hH i j)).mul (hPair i j)))
  apply integrable_local_supported hΩ c hcompact hsupp _ ((h.contDiffOn_density hK).mul hform)
  intro y hy
  simp [fischerHessianForm, finitePolynomialField_zero_outside b c hy, fischerInner_zero_left]

lemma fullCovectorCurvatureContraction_zero (g : MetricField) (e : Frame) (y : X) :
    fullCovectorCurvatureContraction g e y 0 = 0 := by
  simp [fullCovectorCurvatureContraction, fischerInner_zero_left]

lemma fischer_mixed_first_global {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hsupp : tsupport c ⊆ Ω) (y : X) :
    fischerMixedCross g e b c f k (-1) 1 y = fischerMixedTrace g e b c f k 1 (-1) y -
      fischerHessianForm g e b c f k y + fullCovectorCurvatureContraction g e y (finitePolynomialField b c y) := by
  by_cases hy : y ∈ Ω
  · exact loweredWeighted_mixed_first_pointwise hΩ h hK e he hframe b c f k hc hf hy
  · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
    simp [fischerMixedCross, fischerMixedTrace, fischerHessianForm,
      finitePolynomialField_zero_outside b c hout, fischerInner_zero_left, fullCovectorCurvatureContraction_zero]

lemma integrable_fullCovectorCurvature {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    Integrable (fun y => metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y)) := by
  have hC := integrable_fischerMixedCross hΩ h hK e he b c f k (-1) 1 hc hf hcompact hsupp
  have hB := integrable_fischerMixedTrace hΩ h hK e he b c f k 1 (-1) hc hf hcompact hsupp
  have hH := integrable_fischerHessianForm hΩ h hK e he b c f k hc hf hcompact hsupp
  have heq : (fun y => metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y)) =
      fun y => (metricDensity g y * fischerMixedCross g e b c f k (-1) 1 y -
        metricDensity g y * fischerMixedTrace g e b c f k 1 (-1) y) + metricDensity g y * fischerHessianForm g e b c f k y := by
    funext y
    rw [fischer_mixed_first_global hΩ h hK e he hframe b c f k hc hf hsupp y]
    ring
  rw [heq]
  exact (hC.sub hB).add hH

theorem loweredWeighted_first_integrated_identity {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    loweredWeightedCrossEnergy g e b c f k 1 = loweredWeightedTraceSquare g e b c f k (-1) -
      loweredHessianEnergy g e b c f k + integratedFullCovectorCurvature g e b c := by
  have hB := integrable_fischerMixedTrace hΩ h hK e he b c f k 1 (-1) hc.contDiffOn hf hcompact hsupp
  have hH := integrable_fischerHessianForm hΩ h hK e he b c f k hc.contDiffOn hf hcompact hsupp
  have hE := integrable_fullCovectorCurvature hΩ h hK e he hframe b c f k hc.contDiffOn hf hcompact hsupp
  rw [loweredWeightedCrossEnergy_adjoint hΩ h hK e he hframe b c f k 1 hc hf hcompact hsupp,
    loweredWeightedTraceSquare_adjoint hΩ h hK e he hframe b c f k (-1) hc hf hcompact hsupp]
  simp only [neg_neg]
  change (∫ y, metricDensity g y * fischerMixedCross g e b c f k (-1) 1 y) =
    (∫ y, metricDensity g y * fischerMixedTrace g e b c f k 1 (-1) y) -
      (∫ y, metricDensity g y * fischerHessianForm g e b c f k y) +
      ∫ y, metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y)
  have heq : (fun y => metricDensity g y * fischerMixedCross g e b c f k (-1) 1 y) =
      fun y => (metricDensity g y * fischerMixedTrace g e b c f k 1 (-1) y -
        metricDensity g y * fischerHessianForm g e b c f k y) +
        metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y) := by
    funext y
    rw [fischer_mixed_first_global hΩ h hK e he hframe b c f k hc.contDiffOn hf hsupp y]
    ring
  rw [heq]
  have hsplit := integral_add (hB.sub hH) hE
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, integral_sub hB hH]

lemma fischer_mixed_second_global {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hsupp : tsupport c ⊆ Ω) (y : X) :
    fischerMixedTrace g e b c f k (-1) 1 y = fischerMixedCross g e b c f k 1 (-1) y -
      fischerHessianForm g e b c f k y - fullCovectorCurvatureContraction g e y (finitePolynomialField b c y) := by
  by_cases hy : y ∈ Ω
  · exact loweredWeighted_mixed_second_pointwise hΩ h hK e he hframe b c f k hc hf hy
  · have hout : y ∉ tsupport c := fun ht => hy (hsupp ht)
    simp [fischerMixedCross, fischerMixedTrace, fischerHessianForm,
      finitePolynomialField_zero_outside b c hout, fischerInner_zero_left, fullCovectorCurvatureContraction_zero]

theorem loweredWeighted_second_integrated_identity {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    loweredWeightedTraceSquare g e b c f k 1 = loweredWeightedCrossEnergy g e b c f k (-1) -
      loweredHessianEnergy g e b c f k - integratedFullCovectorCurvature g e b c := by
  have hC := integrable_fischerMixedCross hΩ h hK e he b c f k 1 (-1) hc.contDiffOn hf hcompact hsupp
  have hH := integrable_fischerHessianForm hΩ h hK e he b c f k hc.contDiffOn hf hcompact hsupp
  have hE := integrable_fullCovectorCurvature hΩ h hK e he hframe b c f k hc.contDiffOn hf hcompact hsupp
  rw [loweredWeightedTraceSquare_adjoint hΩ h hK e he hframe b c f k 1 hc hf hcompact hsupp,
    loweredWeightedCrossEnergy_adjoint hΩ h hK e he hframe b c f k (-1) hc hf hcompact hsupp]
  simp only [neg_neg]
  change (∫ y, metricDensity g y * fischerMixedTrace g e b c f k (-1) 1 y) =
    (∫ y, metricDensity g y * fischerMixedCross g e b c f k 1 (-1) y) -
      (∫ y, metricDensity g y * fischerHessianForm g e b c f k y) -
      ∫ y, metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y)
  have heq : (fun y => metricDensity g y * fischerMixedTrace g e b c f k (-1) 1 y) =
      fun y => (metricDensity g y * fischerMixedCross g e b c f k 1 (-1) y -
        metricDensity g y * fischerHessianForm g e b c f k y) -
        metricDensity g y * fullCovectorCurvatureContraction g e y (finitePolynomialField b c y) := by
    funext y
    rw [fischer_mixed_second_global hΩ h hK e he hframe b c f k hc.contDiffOn hf hsupp y]
    ring
  rw [heq]
  have hsplit := integral_sub (hC.sub hH) hE
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, integral_sub hC hH]

end ShrinkingSpheres
