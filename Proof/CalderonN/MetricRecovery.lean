module

public import Proof.CalderonN.MetricSystem

import Proof.CalderonN.Hessian
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.NormalizedMetric
import Mathlib.Tactic.Ring

public section

noncomputable section
open Matrix Set
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- At each center the row for the paired Hessian is composed with the
normalized inverse metric on the right side of the trace equation. -/
@[expose] def hessianRecoveryCoeff {n : ℕ} (γ Q : (Mat dim)) (Hess : Fin n → (Mat dim))
    (ij : (I dim) × (I dim)) (v : Fin n × (I dim) × (I dim)) : ℝ :=
  let A := metricSystemMatrix γ Hess
  let L := (A.transpose * A)⁻¹ * A.transpose
  Neg.neg (L ij (.inl v.1) * Q v.2.2 v.2.1)

theorem eq_sum_hessianRecoveryCoeff {n : ℕ} (γ Q H : (Mat dim)) (Hess Diff : Fin n → (Mat dim))
    (hH : H.transpose = H)
    (hvalues : ∀ a, (H * Hess a).trace = -(Q * Diff a).trace)
    (htrace : (γ * H).trace = 0)
    (hdet : let A := metricSystemMatrix γ Hess; (A.transpose * A).det ≠ 0)
    (ij : (I dim) × (I dim)) :
    H ij.1 ij.2 = ∑ v : Fin n × (I dim) × (I dim),
      hessianRecoveryCoeff γ Q Hess ij v * Diff v.1 v.2.1 v.2.2 := by
  let A := metricSystemMatrix γ Hess
  let L := (A.transpose * A)⁻¹ * A.transpose
  let w (q : (I dim) × (I dim)) := H q.1 q.2
  let b : MetricSystemRow dim n → ℝ := fun q =>
    match q with
    | .inl a => -(Q * Diff a).trace
    | .inr _ => 0
  have hb : A *ᵥ w = b := by
    funext row
    rcases row with a | (⟨⟩ | ⟨i, j⟩)
    · exact (metricSystemMatrix_hessian γ Hess H a).trans (hvalues a)
    · exact (metricSystemMatrix_trace γ Hess H).trans htrace
    · rw [show (A *ᵥ w) (.inr (.inr (i, j))) = H i j - H j i from
        metricSystemMatrix_symmetry γ Hess H i j,
        show H i j = H j i from (congrFun (congrFun hH j) i)]
      exact sub_self _
  have hleft : L * A = 1 := gram_left_inverse_of_det_ne_zero hdet
  have hw : L *ᵥ b = w := by rw [← hb, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hcontract (a : Fin n) : (Q * Diff a).trace =
      ∑ i : (I dim), ∑ j : (I dim), Q j i * Diff a i j := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, mul_comm]
  calc
    H ij.1 ij.2 = (L *ᵥ b) ij := (congrFun hw ij).symm
    _ = ∑ v : Fin n × (I dim) × (I dim),
        hessianRecoveryCoeff γ Q Hess ij v * Diff v.1 v.2.1 v.2.2 := by
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, b, mul_zero,
        Finset.sum_const_zero, add_zero, Fintype.sum_prod_type, hcontract, mul_neg]
      apply Finset.sum_congr rfl fun a _ => ?_
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      change -(L ij (.inl a) * (Q j i * Diff a i j)) = -(L ij (.inl a) * Q j i) * Diff a i j
      ring

theorem contDiffOn_metricSystemMatrix_entries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {U : Set E}
    {γ : E → (Mat dim)} {Hess : E → Fin n → (Mat dim)}
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun x => γ x i j) U)
    (hHess : ∀ a i j, ContDiffOn ℝ ∞ (fun x => Hess x a i j) U)
    (r : MetricSystemRow dim n) (ij : (I dim) × (I dim)) :
    ContDiffOn ℝ ∞ (fun x => metricSystemMatrix (γ x) (Hess x) r ij) U := by
  rcases r with a | (⟨⟩ | ⟨i, j⟩)
  · exact hHess a ij.2 ij.1
  · exact hγ ij.2 ij.1
  · exact contDiffOn_const

theorem contDiffOn_hessianRecoveryCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {U : Set E}
    {γ Q : E → (Mat dim)} {Hess : E → Fin n → (Mat dim)}
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun x => γ x i j) U)
    (hQ : ∀ i j, ContDiffOn ℝ ∞ (fun x => Q x i j) U)
    (hHess : ∀ a i j, ContDiffOn ℝ ∞ (fun x => Hess x a i j) U)
    (hdet : ∀ x ∈ U, let A := metricSystemMatrix (γ x) (Hess x); (A.transpose * A).det ≠ 0)
    (ij : (I dim) × (I dim)) (v : Fin n × (I dim) × (I dim)) :
    ContDiffOn ℝ ∞ (fun x => hessianRecoveryCoeff (γ x) (Q x) (Hess x) ij v) U :=
  ((contDiffOn_gram_leftInverse_entry (contDiffOn_metricSystemMatrix_entries hγ hHess) hdet
    ij (Sum.inl v.1)).mul (hQ v.2.2 v.2.1)).neg

end CalderonN
