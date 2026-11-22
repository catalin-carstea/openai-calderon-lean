module

public import Proof.CalderonN.EvaluatedFields
import Mathlib.Tactic

@[expose] public section

/- Port of CurvaturePolynomialFields.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}
variable [NeZero n]

open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

lemma movingFrameCoordinate_vertical {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (e : (Frame n)) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : (X n)} (hy : y ∈ Ω) (w b : (X n)) (i : (I n)) :
    fderiv ℝ (movingFrameCoordinate g e i) (y,w) (0,b) = metricPair g y b (e y i) := by
  rw [fderiv_movingFrameCoordinate hΩ h e he hy]
  simp [metricDifferential_apply, metricPair]

lemma movingFramePolynomial_vertical {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (e : (Frame n)) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : (X n)} (hy : y ∈ Ω) (w b : (X n)) (p : MvPolynomial (I n) ℝ) :
    fderiv ℝ (movingFramePolynomial g e p) (y,w) (0,b) =
      ∑ i, metricPair g y b (e y i) * eval (fun j => movingFrameCoordinate g e j (y,w)) (pderiv i p) := by
  rw [fderiv_movingFramePolynomial hΩ h e he hy]
  simp_rw [movingFrameCoordinate_vertical hΩ h e he hy]

lemma metricCurvature_frame_expansion (g : (MetricField n)) (e : (Frame n)) (y a b w : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    metricCurvature g y a b w =
      ∑ j, movingFrameCoordinate g e j (y,w) • metricCurvature g y a b (e y j) := by
  have hh := congrArg (curvatureLinear (connectionBilinear g) y a b) ((frameBasis g e y hframe).sum_repr w)
  simpa only [map_sum, map_smul, frameBasis_apply, frameBasis_repr, curvatureLinear_apply,
    metricCurvature, movingFrameCoordinate] using hh.symm

lemma metricCurvature_frame_pair (g : (MetricField n)) (e : (Frame n)) (y a b w : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (i : (I n)) :
    metricPair g y (metricCurvature g y a b w) (e y i) =
      ∑ j, frameCurvatureCoefficient g e y a b j i * movingFrameCoordinate g e j (y,w) := by
  rw [metricCurvature_frame_expansion g e y a b w hframe]
  simp only [metricPair_sum_left, metricPair_smul_left, frameCurvatureCoefficient]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The vertical curvature action is exactly the polynomial action in the moving frame. -/
theorem movingFramePolynomial_vertical_curvature {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (e : (Frame n)) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : (X n)} (hy : y ∈ Ω)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (w a b : (X n)) (p : MvPolynomial (I n) ℝ) :
    fderiv ℝ (movingFramePolynomial g e p) (y,w) (0, -metricCurvature g y a b w) =
      movingFramePolynomial g e (curvaturePolynomialAction g e y a b p) (y,w) := by
  rw [movingFramePolynomial_vertical hΩ h e he hy]
  have hneg (v : (X n)) (i : (I n)) : metricPair g y (-v) (e y i) = -metricPair g y v (e y i) := by
    simp only [← metricBilinear_apply, map_neg, _root_.neg_apply]
  simp_rw [hneg, metricCurvature_frame_pair g e y a b w hframe]
  simp only [movingFramePolynomial, curvaturePolynomialAction, polynomialConnectionAction,
    map_sum, map_mul, eval_C, eval_X, map_neg, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {ι : Type*} [Fintype ι]

theorem evaluatedPolynomialField_vertical_curvature {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (e : (Frame n)) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) {y : (X n)} (hy : y ∈ Ω)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hc : DifferentiableAt ℝ c y) (w a v : (X n)) :
    fderiv ℝ (evaluatedPolynomialField g e b c) (y,w) (0, -metricCurvature g y a v w) =
      movingFramePolynomial g e (curvaturePolynomialAction g e y a v (finitePolynomialField b c y)) (y,w) := by
  have hbase := hc.hasFDerivAt.comp (y,w) (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,w)))
  have hcoef (t : ι) := (ContinuousLinearMap.proj t : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (y,w) hbase
  have hpoly (t : ι) := ((contDiffAt_movingFramePolynomial hΩ h e he hy w (b t)).differentiableAt (by simp)).hasFDerivAt
  have hh := HasFDerivAt.sum (u := Finset.univ) (fun t _ => (hcoef t).mul (hpoly t))
  have hfun : evaluatedPolynomialField g e b c =
      ∑ t, ((ContinuousLinearMap.proj t : (ι → ℝ) →L[ℝ] ℝ) ∘ c ∘ Prod.fst) * movingFramePolynomial g e (b t) := by
    funext z
    simp [evaluatedPolynomialField_sum]
  rw [hfun, hh.fderiv]
  simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, map_zero,
    Pi.zero_apply, mul_zero, add_zero]
  simp_rw [movingFramePolynomial_vertical_curvature hΩ h e he hy hframe]
  rw [curvaturePolynomialAction, polynomialConnectionAction_finite]
  simp only [movingFramePolynomial, smul_eq_C_mul, map_sum, map_mul, eval_C,
    Function.comp_apply, ContinuousLinearMap.proj_apply, curvaturePolynomialAction]

end CalderonN
