module

public import Proof.CalderonN.MetricVolumeDifferential

import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

public section

/-! LinearMetric from the checked 3D Theorem 3.1 release 55d37bfe, with arbitrary ambient dimension. -/

noncomputable section
open Set Matrix
open scoped ContDiff Matrix BigOperators

namespace CalderonN

variable {n : ℕ} [NeZero n]

/-- Matrix of a linear change of the common Euclidean coordinates. -/
@[expose] def coordinateMatrix (A : (X n) →L[ℝ] (X n)) : (Mat n) :=
  Matrix.toEuclideanLin.symm A.toLinearMap

theorem coordinateMatrix_mulVec (A : (X n) →L[ℝ] (X n)) (v : (X n)) :
    coordinateMatrix A *ᵥ (fun j => v j) = fun i => A v i := by
  have h := LinearEquiv.apply_symm_apply Matrix.toEuclideanLin A.toLinearMap
  exact congrArg (fun T : (X n) →ₗ[ℝ] (X n) => (T v).ofLp) h

theorem coordinateMatrix_apply (A : (X n) →L[ℝ] (X n)) (i j : (I n)) :
    coordinateMatrix A i j = A (axis j) i := by
  have h := congrFun (coordinateMatrix_mulVec A (axis j)) i
  simpa [axis, Matrix.mulVec, dotProduct, PiLp.single_apply, mul_ite] using h

theorem coordinateMatrix_comp (A B : (X n) →L[ℝ] (X n)) :
    coordinateMatrix (A.comp B) = coordinateMatrix A * coordinateMatrix B :=
  Matrix.toLpLin_symm_comp 2 2 2 A.toLinearMap B.toLinearMap

@[simp] theorem coordinateMatrix_id : coordinateMatrix (ContinuousLinearMap.id ℝ (X n)) = 1 :=
  Matrix.toLpLin_symm_id 2

theorem coordinateMatrix_symm_mul (A : (X n) ≃L[ℝ] (X n)) :
    coordinateMatrix A.symm.toContinuousLinearMap * coordinateMatrix A.toContinuousLinearMap = 1 := by
  have h : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap = ContinuousLinearMap.id ℝ (X n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact A.symm_apply_apply x
  rw [← coordinateMatrix_comp, h, coordinateMatrix_id]

theorem coordinateMatrix_mul_symm (A : (X n) ≃L[ℝ] (X n)) :
    coordinateMatrix A.toContinuousLinearMap * coordinateMatrix A.symm.toContinuousLinearMap = 1 := by
  simpa only [ContinuousLinearEquiv.symm_symm] using coordinateMatrix_symm_mul A.symm

theorem coordinateMatrix_det_ne_zero (A : (X n) ≃L[ℝ] (X n)) :
    (coordinateMatrix A.toContinuousLinearMap).det ≠ 0 := by
  have h := congrArg Matrix.det (coordinateMatrix_mul_symm A)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem coordinateMatrix_symm_eq_inv (A : (X n) ≃L[ℝ] (X n)) :
    coordinateMatrix A.symm.toContinuousLinearMap = (coordinateMatrix A.toContinuousLinearMap)⁻¹ :=
  (Matrix.inv_eq_left_inv (coordinateMatrix_symm_mul A)).symm

theorem coordinateMatrix_det_eq (A : (X n) →L[ℝ] (X n)) :
    (coordinateMatrix A).det = LinearMap.det A.toLinearMap := by
  have h := LinearMap.det_toLpLin 2 (coordinateMatrix A)
  simpa [coordinateMatrix] using h.symm

/-- The covariant metric in the linearly changed harmonic chart. -/
@[expose] def linearPullbackMetric (g : (MetricField n)) (A : (X n) ≃L[ℝ] (X n)) (y : (X n)) : (Mat n) :=
  (coordinateMatrix A.toContinuousLinearMap)ᵀ * g (A y) * coordinateMatrix A.toContinuousLinearMap

theorem smoothMetric_linearPullback {U : Set (X n)} {g : (MetricField n)} (hg : SmoothMetric U g)
    (A : (X n) ≃L[ℝ] (X n)) : SmoothMetric (A ⁻¹' U) (linearPullbackMetric g A) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [linearPullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiffOn.sum fun k _ => (ContDiffOn.sum fun l _ => contDiffOn_const.mul
      ((hg.1 l k).comp A.toContinuousLinearMap.contDiff.contDiffOn (fun _ hx => hx))).mul contDiffOn_const
  · intro y hy
    unfold linearPullbackMetric
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    apply (hg.2 (A y) hy).conjTranspose_mul_mul_same
    exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (coordinateMatrix_det_ne_zero A)))

theorem linearPullbackMetric_volume (g : (MetricField n)) (A : (X n) ≃L[ℝ] (X n)) (y : (X n)) :
    chartVolume (linearPullbackMetric g A) y =
      |(coordinateMatrix A.toContinuousLinearMap).det| * chartVolume g (A y) := by
  unfold chartVolume linearPullbackMetric
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [show (coordinateMatrix A.toContinuousLinearMap).det * (g (A y)).det *
    (coordinateMatrix A.toContinuousLinearMap).det =
      (coordinateMatrix A.toContinuousLinearMap).det ^ 2 * (g (A y)).det by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem linearPullbackMetric_inv (g : (MetricField n)) (A : (X n) ≃L[ℝ] (X n)) (y : (X n)) :
    (linearPullbackMetric g A y)⁻¹ = coordinateMatrix A.symm.toContinuousLinearMap *
      (g (A y))⁻¹ * (coordinateMatrix A.symm.toContinuousLinearMap)ᵀ := by
  rw [linearPullbackMetric, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc, ← coordinateMatrix_symm_eq_inv A]

theorem vector_eq_sum_axis (v : (X n)) : (∑ k : (I n), v k • axis k) = v := by
  ext j
  simp [axis, Pi.single_apply, mul_ite]

theorem coordDeriv_linear_comp (A : (X n) →L[ℝ] (X n)) {f : (X n) → ℝ} {y : (X n)}
    (hf : DifferentiableAt ℝ f (A y)) (i : (I n)) :
    coordDeriv i (f ∘ A) y = ∑ k : (I n), coordinateMatrix A k i * coordDeriv k f (A y) := by
  rw [coordDeriv, (hf.hasFDerivAt.comp y A.hasFDerivAt).fderiv]
  change fderiv ℝ f (A y) (A (axis i)) = _
  conv_lhs => rw [← vector_eq_sum_axis (A (axis i))]
  simp only [map_sum, map_smul, smul_eq_mul, coordDeriv, coordinateMatrix_apply]

end CalderonN
