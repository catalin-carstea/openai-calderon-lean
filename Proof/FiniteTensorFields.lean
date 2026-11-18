import Proof.WeightedTensorFischer
import Proof.WeightedContractedCovectorAdjoint

noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ] [DecidableEq σ]

lemma covariantPolynomialDerivative_congr {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (d : κ → MvPolynomial I ℝ) (c : X → ι → ℝ) (z : X → κ → ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω)
    (hfields : ∀ x ∈ Ω, finitePolynomialField b c x = finitePolynomialField d z x)
    {y : X} (hy : y ∈ Ω) (a : X) :
    covariantPolynomialDerivative g e b c y a = covariantPolynomialDerivative g e d z y a := by
  apply movingFramePolynomial_injective g e y (hframe y hy)
  intro w
  have heval : evaluatedPolynomialField g e b c =ᶠ[nhds (y,w)] evaluatedPolynomialField g e d z := by
    filter_upwards [(hΩ.preimage continuous_fst).mem_nhds hy] with v hv
    simp only [evaluatedPolynomialField, hfields v.1 hv]
  have hd := congrArg (fun L : X × X →L[ℝ] ℝ => L (a, -connection g y a w)) heval.fderiv_eq
  change horizontal g (evaluatedPolynomialField g e b c) y w a =
    horizontal g (evaluatedPolynomialField g e d z) y w a at hd
  rw [evaluatedPolynomialField_horizontal hΩ h hK e he hframe b c hy
      ((hc.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)),
    evaluatedPolynomialField_horizontal hΩ h hK e he hframe d z hy
      ((hz.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))] at hd
  exact hd

def indexedPolynomialFamily (b : ι → MvPolynomial I ℝ) : (σ × ι) → σ → MvPolynomial I ℝ :=
  fun a i => if a.1 = i then b a.2 else 0

def indexedCoefficientFamily (c : X → σ → ι → ℝ) (x : X) : σ × ι → ℝ := fun a => c x a.1 a.2

lemma finitePolynomialField_indexed (b : ι → MvPolynomial I ℝ) (c : X → σ → ι → ℝ) (y : X) (i : σ) :
    finitePolynomialField (fun a => indexedPolynomialFamily b a i) (indexedCoefficientFamily c) y =
      finitePolynomialField b (fun x => c x i) y := by
  simp only [finitePolynomialField, indexedPolynomialFamily, indexedCoefficientFamily, Fintype.sum_prod_type]
  simp

lemma indexedCoefficientFamily_smoothOn {Ω : Set X} (c : X → σ → ι → ℝ)
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) Ω) :
    ContDiffOn ℝ ∞ (indexedCoefficientFamily c) Ω := by
  apply contDiffOn_pi.mpr
  intro a
  exact contDiffOn_pi.mp (hc a.1) a.2

def weightedIndexedCoefficientFamily (g : MetricField) (e : Frame) (c : X → ι → ℝ)
    (f : X → ℝ) (k t : ℝ) (x : X) (i : I) : (ι ⊕ (I × I × ι)) ⊕ ι → ℝ :=
  weightedDerivativeCoefficientFamily g e c f k t (fun y => e y i) x

lemma weightedIndexed_flat_smoothOn {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) Ω :=
  indexedCoefficientFamily_smoothOn _ (fun i => weightedDerivativeCoefficientFamily_smoothOn hΩ h hK e he c f k t _ hc hf (he i))

lemma weightedIndexed_flat_tsupport (g : MetricField) (e : Frame) (c : X → ι → ℝ)
    (f : X → ℝ) (k t : ℝ) :
    tsupport (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) ⊆ tsupport c := by
  apply closure_minimal _ (isClosed_tsupport c)
  intro x hx
  by_contra hout
  have hz (i : I) : weightedDerivativeCoefficientFamily g e c f k t (fun y => e y i) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hout (weightedDerivativeCoefficientFamily_tsupport g e c f k t _ ht))
  apply hx
  funext a
  exact congrFun (hz a.1) a.2

lemma weightedIndexed_flat_smooth_compact {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f Ω) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Ω) :
    ContDiff ℝ ∞ (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) ∧
      HasCompactSupport (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) ∧
      tsupport (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) ⊆ tsupport c := by
  have ht := weightedIndexed_flat_tsupport g e c f k t
  exact ⟨contDiff_of_tsupport_subset hΩ _ (weightedIndexed_flat_smoothOn hΩ h hK e he c f k t hc.contDiffOn hf)
    (ht.trans hsupp), hcompact.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩

lemma finitePolynomialField_weighted_indexed (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ) (y : X) (i : I) :
    finitePolynomialField (fun a => indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a i)
      (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) y =
      weightedPolynomialDerivative g e b c f k t y (e y i) := by
  rw [finitePolynomialField_indexed]
  exact (weightedPolynomialDerivative_eq_finite g e b c f k t _ y).symm

lemma finitePolynomialField_weighted_lowered (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ) (y : X) (i l : I) :
    finitePolynomialField (fun a => pderiv l (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a i))
      (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) y =
      weightedCovectorPolynomialDerivative g e (fun a h => pderiv h (b a)) c f k t y (e y i) l := by
  rw [finitePolynomialField_partial, finitePolynomialField_weighted_indexed, weightedCovectorPolynomialDerivative_partial]

lemma covectorPolynomialDerivative_weighted_lowered {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) (a : X) (j l : I) :
    covectorPolynomialDerivative g e (fun q h => pderiv h (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) q j))
      (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) y a l =
      covectorPolynomialDerivative g e (fun q h => pderiv h (weightedDerivativePolynomialFamily b q))
        (weightedDerivativeCoefficientFamily g e c f k t (fun x => e x j)) y a l := by
  rw [covectorPolynomialDerivative_partial, covectorPolynomialDerivative_partial]
  apply congrArg (pderiv l)
  apply covariantPolynomialDerivative_congr hΩ h hK e he hframe _ _ _ _
    (weightedIndexed_flat_smoothOn hΩ h hK e he c f k t hc hf)
    (weightedDerivativeCoefficientFamily_smoothOn hΩ h hK e he c f k t _ hc hf (he j)) _ hy
  intro x hx
  rw [finitePolynomialField_indexed]
  rfl

lemma weightedTensorPolynomialDerivative_weighted_lowered {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) (i j l : I) :
    weightedTensorPolynomialDerivative g e (fun a h q => pderiv q (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a h))
      (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) f k s y (e y i) j l =
      weightedLoweredIndexedHessian g e b c f k s t y i j l := by
  simp only [weightedTensorPolynomialDerivative, tensorPolynomialDerivative,
    weightedLoweredIndexedHessian, weightedCovectorPolynomialDerivative]
  rw [covectorPolynomialDerivative_weighted_lowered hΩ h hK e he hframe b c f k t hc hf hy]
  simp_rw [finitePolynomialField_weighted_lowered]
  rw [weightedCovectorPolynomialDerivative_partial g e b c f k t y (e y j) l,
    weightedPolynomialDerivative_eq_finite g e b c f k t (fun x => e x j) y]
  simp only [finitePolynomialField_partial, weightedCovectorPolynomialDerivative]
  ring

def weightedTracePolynomialFamily (b : ι → MvPolynomial I ℝ) :
    I × ((ι ⊕ (I × I × ι)) ⊕ ι) → MvPolynomial I ℝ :=
  fun a => ∑ i, pderiv i (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a i)

lemma finitePolynomialField_weighted_trace (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ) (y : X) :
    finitePolynomialField (weightedTracePolynomialFamily b)
      (indexedCoefficientFamily (weightedIndexedCoefficientFamily g e c f k t)) y =
      ∑ i, weightedCovectorPolynomialDerivative g e (fun a h => pderiv h (b a)) c f k t y (e y i) i := by
  unfold weightedTracePolynomialFamily
  simp only [finitePolynomialField, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [finitePolynomialField] using (finitePolynomialField_weighted_lowered g e b c f k t y i i)

lemma weightedTensorPolynomialDerivative_transpose (g : MetricField) (e : Frame)
    (b : ι → I → I → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) (y a : X) (i j : I) :
    weightedTensorPolynomialDerivative g e (fun q h l => b q l h) c f k s y a i j =
      weightedTensorPolynomialDerivative g e b c f k s y a j i := by
  simp only [weightedTensorPolynomialDerivative, tensorPolynomialDerivative, covectorPolynomialDerivative]
  ring

lemma finitePolynomialField_sum_family (b : ι → σ → MvPolynomial I ℝ) (c : X → ι → ℝ) (y : X) :
    finitePolynomialField (fun a => ∑ i, b a i) c y = ∑ i, finitePolynomialField (fun a => b a i) c y := by
  simp only [finitePolynomialField, Finset.smul_sum]
  exact Finset.sum_comm

lemma covariantPolynomialDerivative_sum_family (g : MetricField) (e : Frame)
    (b : ι → σ → MvPolynomial I ℝ) (c : X → ι → ℝ) (y a : X) :
    covariantPolynomialDerivative g e (fun q => ∑ i, b q i) c y a =
      ∑ i, covariantPolynomialDerivative g e (fun q => b q i) c y a := by
  have hd : finitePolynomialFieldDerivative (fun q => ∑ i, b q i) c y a =
      ∑ i, finitePolynomialFieldDerivative (fun q => b q i) c y a := by
    simp only [finitePolynomialFieldDerivative, Finset.smul_sum]
    exact Finset.sum_comm
  have hA : polynomialConnectionAction (frameConnectionCoefficient g e y a)
      (∑ i, finitePolynomialField (fun q => b q i) c y) =
      ∑ i, polynomialConnectionAction (frameConnectionCoefficient g e y a) (finitePolynomialField (fun q => b q i) c y) := by
    change polynomialConnectionLinear (frameConnectionCoefficient g e y a)
      (∑ i, finitePolynomialField (fun q => b q i) c y) =
      ∑ i, polynomialConnectionLinear (frameConnectionCoefficient g e y a) (finitePolynomialField (fun q => b q i) c y)
    simp only [map_sum]
  simp only [covariantPolynomialDerivative, finitePolynomialField_sum_family, hd, hA, Finset.sum_add_distrib]

lemma skew_tensor_trace_cancellation (w : I → I → ℝ) (hw : ∀ a i, w a i = -w i a)
    (T : I → I → MvPolynomial I ℝ) :
    (∑ i, ∑ a, C (w i a) * T a i) + (∑ i, ∑ a, C (w i a) * T i a) = 0 := by
  have hh : (∑ i, ∑ a, C (w i a) * T a i) = -(∑ i, ∑ a, C (w i a) * T i a) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    rw [hw a i, map_neg, neg_mul]
  rw [hh, neg_add_cancel]

lemma weightedPolynomialDerivative_tensorTrace {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → I → I → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ)
    {y : X} (hy : y ∈ Ω) (a : X) :
    weightedPolynomialDerivative g e (fun q => ∑ i, b q i i) c f k s y a =
      ∑ i, weightedTensorPolynomialDerivative g e b c f k s y a i i := by
  have hh := skew_tensor_trace_cancellation (frameConnectionCoefficient g e y a)
    (frameConnection_skew hΩ h hK e he hframe hy a) (fun i j => finitePolynomialField (fun q => b q i j) c y)
  have hq := covariantPolynomialDerivative_sum_family g e (fun q i => b q i i) c y a
  have hu := finitePolynomialField_sum_family (fun q i => b q i i) c y
  simp only [weightedPolynomialDerivative, weightedTensorPolynomialDerivative, tensorPolynomialDerivative,
    covectorPolynomialDerivative, Fin.sum_univ_three] at *
  rw [hq, hu]
  linear_combination C s * hh

end ShrinkingSpheres
