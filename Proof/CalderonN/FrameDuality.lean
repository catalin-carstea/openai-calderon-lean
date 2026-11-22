module

public import Proof.CalderonN.SphereFrame
import Mathlib.Tactic.Ring
import Mathlib.Tactic

@[expose] public section

/- Port of FrameDuality.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

def frameMatrix (e : (Frame n)) (y : (X n)) : (Mat n) := fun i j => e y j i

lemma frameMatrix_gram (γ : (MetricField n)) (e : (Frame n)) (y : (X n))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) :
    (frameMatrix e y).transpose * γ y * frameMatrix e y = 1 := by
  ext i j
  simp only [Matrix.one_apply]
  rw [← he i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, frameMatrix, metricPair,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma inverse_metric_of_frame (γ : (MetricField n)) (e : (Frame n)) (y : (X n))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) :
    (γ y)⁻¹ = frameMatrix e y * (frameMatrix e y).transpose := by
  have h := mul_eq_one_comm.mp (frameMatrix_gram γ e y he)
  rw [← Matrix.mul_assoc] at h
  exact Matrix.inv_eq_left_inv h

lemma linear_axis_expansion (L : (X n) →L[ℝ] ℝ) (v : (X n)) :
    L v = ∑ i, v i * L (axis i) := by
  have h := congrArg L ((EuclideanSpace.basisFun (I n) ℝ).sum_repr v)
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, axis, smul_eq_mul] using h.symm

/-- The norm of a covector computed in any orthonormal frame equals its inverse-metric norm. -/
lemma sum_frame_derivative_sq (γ : (MetricField n)) (e : (Frame n)) (y : (X n))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (L : (X n) →L[ℝ] ℝ) :
    (∑ i, (L (e y i))^2) = ∑ i, ∑ j, (γ y)⁻¹ i j * L (axis i) * L (axis j) := by
  rw [inverse_metric_of_frame γ e y he]
  have hL (i : (I n)) := linear_axis_expansion L (e y i)
  simp_rw [hL, pow_two]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, frameMatrix, Finset.sum_mul, Finset.mul_sum]
  conv_rhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma beta_sq (γ : (MetricField n)) (e : (Frame n)) (r : (X n) → ℝ) (y : (X n))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) :
    (beta γ r y)^2 = ∑ i, (fderiv ℝ (fun x => Real.log (r x)) y (e y i))^2 := by
  have h := sum_frame_derivative_sq γ e y he (fderiv ℝ (fun x => Real.log (r x)) y)
  unfold beta
  change (Real.sqrt (∑ i, ∑ j, (γ y)⁻¹ i j * coordDeriv i (fun x => Real.log (r x)) y *
    coordDeriv j (fun x => Real.log (r x)) y))^2 = _
  simp only [coordDeriv]
  rw [← h]
  exact Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CalderonN
