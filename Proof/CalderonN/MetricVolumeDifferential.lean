module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Matrix.Normed

import Proof.CalderonN.DetIdentity
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Tactic.FieldSimp

/-! Adapted from `Calderon/MetricVolumeDifferential.lean` and
`Calderon/MetricInverseDifferential.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

noncomputable section
open scoped Matrix.Norms.Operator ContDiff
namespace CalderonN

variable {n : ℕ}

def chartVolume (g : MetricField n) (x : X n) : ℝ := Real.sqrt (g x).det

def determinantDerivative (M : (Mat n)) : (Mat n) →L[ℝ] ℝ :=
  M.det • ((Matrix.traceLinearMap ((I n)) ℝ ℝ).toContinuousLinearMap.comp
    (LinearMap.mulLeft ℝ (M⁻¹)).toContinuousLinearMap)

lemma determinantDerivative_apply (M H : (Mat n)) :
    determinantDerivative M H = M.det * Matrix.trace (M⁻¹ * H) := rfl

lemma hasFDerivAt_det_of_isUnit (M : (Mat n)) (hM : IsUnit M.det) :
    HasFDerivAt (Matrix.det : (Mat n) → ℝ) (determinantDerivative M) M := by
  let L : (Mat n) →L[ℝ] (Mat n) := (LinearMap.mulLeft ℝ (M⁻¹)).toContinuousLinearMap
  have hL : L M = 1 := Matrix.nonsing_inv_mul M hM
  have hI : HasFDerivAt (Matrix.det : (Mat n) → ℝ)
      (Matrix.traceLinearMap ((I n)) ℝ ℝ).toContinuousLinearMap (L M) := by
    rw [hL]
    exact Matrix.hasFDerivAt_det_one
  have h := (hI.comp M L.hasFDerivAt).const_mul M.det
  have hprod : M.det * (M⁻¹).det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv M hM, Matrix.det_one]
  have he : (fun Y : (Mat n) => M.det * Matrix.det (L Y)) = Matrix.det := by
    funext Y
    change M.det * Matrix.det (M⁻¹ * Y) = Matrix.det Y
    rw [Matrix.det_mul, ← mul_assoc, hprod, one_mul]
  change HasFDerivAt (fun Y : (Mat n) => M.det * Matrix.det (L Y))
    (determinantDerivative M) M at h
  rwa [he] at h

def matrixFieldDerivative (g : (MetricField n)) (x : (X n)) : (X n) →L[ℝ] (Mat n) :=
  ∑ i : (I n), ∑ j : (I n),
    (fderiv ℝ (fun y => g y i j) x).smulRight (Matrix.single i j (1 : ℝ))

lemma matrixFieldDerivative_apply_entry (g : (MetricField n)) (x V : (X n)) (i j : (I n)) :
    matrixFieldDerivative g x V i j = fderiv ℝ (fun y => g y i j) x V := by
  classical
  have h := Matrix.sum_sum_single (fun a b : (I n) =>
    fderiv ℝ (fun y => g y a b) x V)
  simpa [matrixFieldDerivative] using congrArg (fun H : (Mat n) => H i j) h

lemma hasFDerivAt_matrixField_of_entries (g : (MetricField n)) (x : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) :
    HasFDerivAt g (matrixFieldDerivative g x) x := by
  classical
  have h : HasFDerivAt
      (fun y => ∑ i : (I n), ∑ j : (I n), g y i j • Matrix.single i j (1 : ℝ))
      (matrixFieldDerivative g x) x :=
    HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ =>
      (hg i j).hasFDerivAt.smul_const (Matrix.single i j (1 : ℝ))
  have he : (fun y => ∑ i : (I n), ∑ j : (I n),
      g y i j • Matrix.single i j (1 : ℝ)) = g := by
    funext y
    calc
      _ = ∑ i : (I n), ∑ j : (I n), Matrix.single i j (g y i j) := by simp
      _ = Matrix.of (g y) := Matrix.sum_sum_single (g y)
      _ = g y := by ext i j; rfl
  rwa [he] at h

lemma hasFDerivAt_metric_determinant (g : (MetricField n)) (x : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    HasFDerivAt (fun y => (g y).det)
      ((determinantDerivative (g x)).comp (matrixFieldDerivative g x)) x :=
  (hasFDerivAt_det_of_isUnit (g x) (isUnit_iff_ne_zero.mpr hp.det_pos.ne')).comp x
    (hasFDerivAt_matrixField_of_entries g x hg)

lemma fderiv_vol_apply (g : (MetricField n)) (x V : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    fderiv ℝ (chartVolume g) x V = (chartVolume g x / 2) *
      Matrix.trace ((g x)⁻¹ * matrixFieldDerivative g x V) := by
  have hd := hasFDerivAt_metric_determinant g x hg hp
  have hs := hd.sqrt hp.det_pos.ne'
  change HasFDerivAt (chartVolume g) ((1 / (2 * chartVolume g x)) •
    (determinantDerivative (g x)).comp (matrixFieldDerivative g x)) x at hs
  have hsq : (chartVolume g x) ^ 2 = (g x).det := Real.sq_sqrt hp.det_pos.le
  have hv : chartVolume g x ≠ 0 := (Real.sqrt_pos.2 hp.det_pos).ne'
  rw [hs.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, determinantDerivative_apply]
  change (1 / (2 * chartVolume g x)) * ((g x).det * _) = _
  rw [← hsq]
  field_simp [hv]

lemma fderiv_vol_apply_entries (g : (MetricField n)) (x V : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    fderiv ℝ (chartVolume g) x V = (chartVolume g x / 2) *
      ∑ i : (I n), ∑ j : (I n),
        (g x)⁻¹ j i * fderiv ℝ (fun y => g y i j) x V := by
  rw [fderiv_vol_apply g x V hg hp]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixFieldDerivative_apply_entry]
  exact Finset.sum_comm

def inverseMatrixDerivative (M : (Mat n)) : (Mat n) →L[ℝ] (Mat n) :=
  -ContinuousLinearMap.mulLeftRight ℝ (Mat n) M⁻¹ M⁻¹

lemma inverseMatrixDerivative_apply (M H : (Mat n)) :
    inverseMatrixDerivative M H = -(M⁻¹ * H * M⁻¹) := rfl

lemma hasFDerivAt_inverseMatrix_of_isUnit (M : (Mat n)) (hM : IsUnit M) :
    HasFDerivAt (fun Y : (Mat n) => Y⁻¹) (inverseMatrixDerivative M) M := by
  obtain ⟨u, hu⟩ := hM
  have hi : (↑u⁻¹ : (Mat n)) = M⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have he : (Ring.inverse : (Mat n) → (Mat n)) = fun Y : (Mat n) => Y⁻¹ := by
    funext Y
    exact (Matrix.nonsing_inv_eq_ringInverse Y).symm
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [he, hi, hu] at h
  exact h

lemma hasFDerivAt_inverseMetric_matrix (g : (MetricField n)) (x : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    HasFDerivAt (fun y => (g y)⁻¹)
      ((inverseMatrixDerivative (g x)).comp (matrixFieldDerivative g x)) x :=
  (hasFDerivAt_inverseMatrix_of_isUnit (g x) hp.isUnit).comp x
    (hasFDerivAt_matrixField_of_entries g x hg)

lemma fderiv_inverseMetric_matrix_apply (g : (MetricField n)) (x V : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    fderiv ℝ (fun y => (g y)⁻¹) x V =
      -((g x)⁻¹ * matrixFieldDerivative g x V * (g x)⁻¹) := by
  rw [(hasFDerivAt_inverseMetric_matrix g x hg hp).fderiv]
  rfl

lemma fderiv_inverseMetric_entry_apply (g : (MetricField n)) (x V : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (i j : (I n)) :
    fderiv ℝ (fun y => (g y)⁻¹ i j) x V =
      -∑ a : (I n), ∑ b : (I n),
        (g x)⁻¹ i a * fderiv ℝ (fun y => g y a b) x V * (g x)⁻¹ b j := by
  let E : (Mat n) →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have h := E.hasFDerivAt.comp x (hasFDerivAt_inverseMetric_matrix g x hg hp)
  change HasFDerivAt (fun y => (g y)⁻¹ i j)
    (E.comp ((inverseMatrixDerivative (g x)).comp (matrixFieldDerivative g x))) x at h
  rw [h.fderiv]
  change -((g x)⁻¹ * matrixFieldDerivative g x V * (g x)⁻¹) i j = _
  simp only [Matrix.mul_apply, matrixFieldDerivative_apply_entry,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

end CalderonN
