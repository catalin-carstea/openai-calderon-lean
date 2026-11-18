import Proof.IntegratedFischerFields

noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

lemma loweredWeightedSecondTensorField_mixed_commutator {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) (i j l : I) :
    loweredWeightedSecondTensorField g e b c f k (-1) 1 y j i l -
      loweredWeightedSecondTensorField g e b c f k 1 (-1) y i j l =
      covectorCurvatureAction g e y (e y i) (e y j) (fun a => pderiv a (finitePolynomialField b c y)) l -
      C (2*k*hessianBilinear g f y (e y i) (e y j)) * pderiv l (finitePolynomialField b c y) := by
  rw [loweredWeightedSecondTensorField_eq_indexed hΩ h hK e he hframe b c f k (-1) 1 hc hf hy,
    loweredWeightedSecondTensorField_eq_indexed hΩ h hK e he hframe b c f k 1 (-1) hc hf hy]
  exact weightedLoweredIndexedHessian_mixed_commutator hΩ h hK e he hframe b c f k hc hf hy i j l

lemma covectorCurvatureAction_partial_antisymm {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Ω)
    {y : X} (hy : y ∈ Ω) (i j l : I) :
    covectorCurvatureAction g e y (e y j) (e y i) (fun a => pderiv a (finitePolynomialField b c y)) l =
      -covectorCurvatureAction g e y (e y i) (e y j) (fun a => pderiv a (finitePolynomialField b c y)) l := by
  rw [covectorCurvatureAction_partial, covectorCurvatureAction_partial,
    ← indexedPolynomialHessian_antisymm hΩ h hK e he hframe b c hc hy i j,
    ← indexedPolynomialHessian_antisymm hΩ h hK e he hframe b c hc hy j i]
  simp only [map_sub]
  abel

lemma loweredWeighted_mixed_first_pointwise {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) :
    (∑ i, ∑ j, fischerInner (pderiv j (finitePolynomialField b c y))
      (loweredWeightedSecondTensorField g e b c f k (-1) 1 y i j i)) =
      (∑ j, ∑ i, fischerInner (pderiv j (finitePolynomialField b c y))
        (loweredWeightedSecondTensorField g e b c f k 1 (-1) y j i i)) -
      (∑ i, ∑ j, (2*k*hessianBilinear g f y (e y i) (e y j)) *
        fischerInner (pderiv i (finitePolynomialField b c y)) (pderiv j (finitePolynomialField b c y))) +
      fullCovectorCurvatureContraction g e y (finitePolynomialField b c y) := by
  have hh (i j : I) := congrArg (fischerInner (pderiv j (finitePolynomialField b c y)))
    (loweredWeightedSecondTensorField_mixed_commutator hΩ h hK e he hframe b c f k hc hf hy j i i)
  simp only [fischerInner_sub_right, fischerInner_C_mul_right] at hh
  have hp (i j : I) : fischerInner (pderiv j (finitePolynomialField b c y))
      (loweredWeightedSecondTensorField g e b c f k (-1) 1 y i j i) =
      fischerInner (pderiv j (finitePolynomialField b c y))
        (loweredWeightedSecondTensorField g e b c f k 1 (-1) y j i i) -
      (2*k*hessianBilinear g f y (e y j) (e y i)) *
        fischerInner (pderiv j (finitePolynomialField b c y)) (pderiv i (finitePolynomialField b c y)) +
      fischerInner (pderiv j (finitePolynomialField b c y))
        (covectorCurvatureAction g e y (e y j) (e y i) (fun a => pderiv a (finitePolynomialField b c y)) i) := by
    linarith only [hh i j]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, fullCovectorCurvatureContraction]
  have hA : (∑ i, ∑ j, fischerInner (pderiv j (finitePolynomialField b c y))
      (loweredWeightedSecondTensorField g e b c f k 1 (-1) y j i i)) =
      ∑ j, ∑ i, fischerInner (pderiv j (finitePolynomialField b c y))
        (loweredWeightedSecondTensorField g e b c f k 1 (-1) y j i i) := Finset.sum_comm
  have hH : (∑ i, ∑ j, (2*k*hessianBilinear g f y (e y j) (e y i)) *
      fischerInner (pderiv j (finitePolynomialField b c y)) (pderiv i (finitePolynomialField b c y))) =
      ∑ i, ∑ j, (2*k*hessianBilinear g f y (e y i) (e y j)) *
        fischerInner (pderiv i (finitePolynomialField b c y)) (pderiv j (finitePolynomialField b c y)) := Finset.sum_comm
  have hE : (∑ i, ∑ j, fischerInner (pderiv j (finitePolynomialField b c y))
      (covectorCurvatureAction g e y (e y j) (e y i) (fun a => pderiv a (finitePolynomialField b c y)) i)) =
      ∑ i, ∑ j, fischerInner (pderiv i (finitePolynomialField b c y))
        (covectorCurvatureAction g e y (e y i) (e y j) (fun a => pderiv a (finitePolynomialField b c y)) j) := Finset.sum_comm
  rw [hA, hH, hE]

lemma loweredWeighted_mixed_second_pointwise {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) :
    (∑ j, ∑ i, fischerInner (pderiv j (finitePolynomialField b c y))
      (loweredWeightedSecondTensorField g e b c f k (-1) 1 y j i i)) =
      (∑ i, ∑ j, fischerInner (pderiv j (finitePolynomialField b c y))
        (loweredWeightedSecondTensorField g e b c f k 1 (-1) y i j i)) -
      (∑ i, ∑ j, (2*k*hessianBilinear g f y (e y i) (e y j)) *
        fischerInner (pderiv i (finitePolynomialField b c y)) (pderiv j (finitePolynomialField b c y))) -
      fullCovectorCurvatureContraction g e y (finitePolynomialField b c y) := by
  have hh (i j : I) := congrArg (fischerInner (pderiv j (finitePolynomialField b c y)))
    (loweredWeightedSecondTensorField_mixed_commutator hΩ h hK e he hframe b c f k hc hf hy i j i)
  simp only [fischerInner_sub_right, fischerInner_C_mul_right] at hh
  have hp (i j : I) : fischerInner (pderiv j (finitePolynomialField b c y))
      (loweredWeightedSecondTensorField g e b c f k (-1) 1 y j i i) =
      fischerInner (pderiv j (finitePolynomialField b c y))
        (loweredWeightedSecondTensorField g e b c f k 1 (-1) y i j i) -
      (2*k*hessianBilinear g f y (e y i) (e y j)) *
        fischerInner (pderiv j (finitePolynomialField b c y)) (pderiv i (finitePolynomialField b c y)) -
      fischerInner (pderiv j (finitePolynomialField b c y))
        (covectorCurvatureAction g e y (e y j) (e y i) (fun a => pderiv a (finitePolynomialField b c y)) i) := by
    rw [covectorCurvatureAction_partial_antisymm hΩ h hK e he hframe b c hc hy i j i, fischerInner_neg_right]
    linarith only [hh i j]
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib, fullCovectorCurvatureContraction]
  have hA : (∑ j, ∑ i, fischerInner (pderiv j (finitePolynomialField b c y))
      (loweredWeightedSecondTensorField g e b c f k 1 (-1) y i j i)) =
      ∑ i, ∑ j, fischerInner (pderiv j (finitePolynomialField b c y))
        (loweredWeightedSecondTensorField g e b c f k 1 (-1) y i j i) := Finset.sum_comm
  have hH : (∑ j, ∑ i, (2*k*hessianBilinear g f y (e y i) (e y j)) *
      fischerInner (pderiv j (finitePolynomialField b c y)) (pderiv i (finitePolynomialField b c y))) =
      ∑ i, ∑ j, (2*k*hessianBilinear g f y (e y i) (e y j)) *
        fischerInner (pderiv i (finitePolynomialField b c y)) (pderiv j (finitePolynomialField b c y)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [fischerInner_symm]
  rw [hA, hH]

end ShrinkingSpheres
