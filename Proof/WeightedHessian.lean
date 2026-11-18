import Proof.WeightedDerivativeFields
import Proof.IndexedPolynomialHessian
import Proof.HessianDifferential

noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

lemma frameDerivative_df {Ω : Set X} (hΩ : IsOpen Ω) {g : MetricField}
    (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (i j : I) :
    fderiv ℝ (fun x => fderiv ℝ f x (e x j)) y (e y i) =
      hessianBilinear g f y (e y i) (e y j) +
      ∑ a, frameConnectionCoefficient g e y (e y i) j a * fderiv ℝ f y (e y a) := by
  have hdf := (((hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).contDiffAt
    (hΩ.mem_nhds hy)).differentiableAt (by simp))
  have hej := ((he j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hrec := congrArg (fderiv ℝ f y) ((frameBasis g e y hframe).sum_repr (covariantFrameVector g e y (e y i) j))
  simp only [map_sum, map_smul, smul_eq_mul, frameBasis_apply] at hrec
  simp_rw [frameBasis_repr] at hrec
  rw [fderiv_clm_apply hdf hej]
  simp only [covariantFrameVector, frameConnectionCoefficient,
    map_add, map_sum, map_smul, smul_eq_mul, _root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hessianBilinear_apply] at hrec ⊢
  linarith

lemma hessianBilinear_symm {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (f : X → ℝ) {y : X} (hy : y ∈ Ω)
    (hf : ContDiffAt ℝ ∞ f y) (a b : X) :
    hessianBilinear g f y a b = hessianBilinear g f y b a := by
  simp only [hessianBilinear_apply]
  rw [(hf.isSymmSndFDerivAt (by simp)).eq a b, connection_symmetric hΩ h hy a b]

variable {ι : Type*} [Fintype ι]

def weightedIndexedPolynomialHessian (g : MetricField) (e : Frame)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ) (y : X) (i j : I) :
    MvPolynomial I ℝ :=
  weightedPolynomialDerivative g e (weightedDerivativePolynomialFamily b)
    (weightedDerivativeCoefficientFamily g e c f k t (fun x => e x j)) f k s y (e y i) -
    C s * ∑ a, C (frameConnectionCoefficient g e y (e y i) j a) *
      weightedPolynomialDerivative g e b c f k t y (e y a)

lemma covariantPolynomialDerivative_weighted_finite {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) (i j : I) :
    covariantPolynomialDerivative g e (weightedDerivativePolynomialFamily b)
      (weightedDerivativeCoefficientFamily g e c f k t (fun x => e x j)) y (e y i) =
      C t * covariantPolynomialDerivative g e (derivativePolynomialFamily b)
        (derivativeCoefficientFamily g e c (fun x => e x j)) y (e y i) +
      C (k*fderiv ℝ f y (e y j)) * covariantPolynomialDerivative g e b c y (e y i) +
      C (k*(hessianBilinear g f y (e y i) (e y j) +
        ∑ a, frameConnectionCoefficient g e y (e y i) j a * fderiv ℝ f y (e y a))) *
          finitePolynomialField b c y := by
  have hq := derivativeCoefficientFamily_smoothOn hΩ h hK e he c (fun x => e x j) hc (he j)
  have hdf : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (e x j)) Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply (he j)
  have hw : ContDiffOn ℝ ∞ (fun x => k*fderiv ℝ f x (e x j)) Ω := contDiffOn_const.mul hdf
  have htc : ContDiffOn ℝ ∞ (fun x => t • derivativeCoefficientFamily g e c (fun x => e x j) x) Ω :=
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => t) Ω).smul hq
  have hwc : ContDiffOn ℝ ∞ (fun x => (k*fderiv ℝ f x (e x j)) • c x) Ω := hw.smul hc
  rw [weightedDerivativePolynomialFamily, weightedDerivativeCoefficientFamily,
    covariantPolynomialDerivative_joined g e (derivativePolynomialFamily b) b _ _ y (e y i)
      ((htc.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hwc.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)),
    covariantPolynomialDerivative_coeff_smul g e _ _ _ y (e y i)
      ((hq.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) (differentiableAt_const t),
    covariantPolynomialDerivative_coeff_smul g e _ _ _ y (e y i)
      ((hc.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hw.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))]
  rw [fderiv_const_mul ((hdf.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) k,
    (hasFDerivAt_const (𝕜 := ℝ) t y).fderiv]
  simp only [zero_apply, map_zero, zero_mul, add_zero, _root_.smul_apply, smul_eq_mul]
  rw [frameDerivative_df hΩ e he f hf hy (hframe y hy)]
  abel

lemma weightedIndexedPolynomialHessian_expansion {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k s t : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) (i j : I) :
    weightedIndexedPolynomialHessian g e b c f k s t y i j =
      C (s*t) * indexedPolynomialHessian g e b c y i j +
      C (s*k*hessianBilinear g f y (e y i) (e y j)) * finitePolynomialField b c y +
      C (s*k*fderiv ℝ f y (e y j)) * covariantPolynomialDerivative g e b c y (e y i) +
      C (t*k*fderiv ℝ f y (e y i)) * covariantPolynomialDerivative g e b c y (e y j) +
      C (k^2*fderiv ℝ f y (e y i)*fderiv ℝ f y (e y j)) * finitePolynomialField b c y := by
  rw [weightedIndexedPolynomialHessian, weightedPolynomialDerivative,
    covariantPolynomialDerivative_weighted_finite hΩ h hK e he hframe b c f k t hc hf hy,
    ← weightedPolynomialDerivative_eq_finite g e b c f k t (fun x => e x j) y]
  simp only [indexedPolynomialHessian, weightedPolynomialDerivative, Fin.sum_univ_three,
    map_mul, map_add, map_pow]
  ring

/-- The mixed weighted commutator contains the Hessian of the same scalar profile and the
    curvature of the actual connection. -/
theorem weightedIndexedPolynomialHessian_mixed_commutator {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (f : X → ℝ) (k : ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) (i j : I) :
    weightedIndexedPolynomialHessian g e b c f k (-1) 1 y j i -
      weightedIndexedPolynomialHessian g e b c f k 1 (-1) y i j =
      curvaturePolynomialAction g e y (e y i) (e y j) (finitePolynomialField b c y) -
      C (2*k*hessianBilinear g f y (e y i) (e y j)) * finitePolynomialField b c y := by
  rw [weightedIndexedPolynomialHessian_expansion hΩ h hK e he hframe b c f k (-1) 1 hc hf hy,
    weightedIndexedPolynomialHessian_expansion hΩ h hK e he hframe b c f k 1 (-1) hc hf hy,
    hessianBilinear_symm hΩ h f hy (hf.contDiffAt (hΩ.mem_nhds hy)) (e y j) (e y i),
    ← indexedPolynomialHessian_antisymm hΩ h hK e he hframe b c hc hy i j]
  simp only [map_mul, map_neg, map_one, map_ofNat]
  ring

end ShrinkingSpheres
