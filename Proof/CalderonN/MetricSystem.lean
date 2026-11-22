module

public import Proof.CalderonN.Chart

import Proof.CalderonN.Hessian
import Proof.CalderonN.MetricCalculus
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Ring

public section

noncomputable section
open Matrix Set Filter
open scoped BigOperators ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev MetricSystemRow (dim n : ℕ) := Fin n ⊕ (Unit ⊕ ((I dim) × (I dim)))

/-- The pointwise system has a row for each Hessian, one metric trace row,
and the symmetry equations. This lets its domain be the full matrix space. -/
@[expose] def metricSystemMatrix {n : ℕ} (γ : (Mat dim)) (Hess : Fin n → (Mat dim)) :
    Matrix (MetricSystemRow dim n) ((I dim) × (I dim)) ℝ :=
  fun row (i, j) =>
    match row with
    | .inl a => Hess a j i
    | .inr (.inl _) => γ j i
    | .inr (.inr (k, l)) => (if (i, j) = (k, l) then 1 else 0) -
        (if (i, j) = (l, k) then 1 else 0)

theorem metricSystemMatrix_hessian {n : ℕ} (γ : (Mat dim)) (Hess : Fin n → (Mat dim))
    (H : (Mat dim)) (a : Fin n) :
    (metricSystemMatrix γ Hess *ᵥ (fun ij => H ij.1 ij.2)) (.inl a) = (H * Hess a).trace := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, metricSystemMatrix,
    Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [mul_comm]

theorem metricSystemMatrix_trace {n : ℕ} (γ : (Mat dim)) (Hess : Fin n → (Mat dim)) (H : (Mat dim)) :
    (metricSystemMatrix γ Hess *ᵥ (fun ij => H ij.1 ij.2)) (.inr (.inl ())) = (γ * H).trace := by
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, metricSystemMatrix,
    Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [mul_comm]

theorem metricSystemMatrix_symmetry {n : ℕ} (γ : (Mat dim)) (Hess : Fin n → (Mat dim)) (H : (Mat dim)) (i j : (I dim)) :
    (metricSystemMatrix γ Hess *ᵥ (fun ij => H ij.1 ij.2)) (.inr (.inr (i, j))) = H i j - H j i := by
  classical
  unfold Matrix.mulVec dotProduct
  change (∑ ij : (I dim) × (I dim), ((if ij = (i, j) then 1 else 0) -
    (if ij = (j, i) then 1 else 0)) * H ij.1 ij.2) = _
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem metricSystemMatrix_injective {n : ℕ} {γ : (Mat dim)} (hγ : γ.PosDef) {Hess : Fin n → (Mat dim)}
    (hspan : ∀ V : (Mat dim), V ∈ Submodule.span ℝ (Set.range Hess) ↔
      V.transpose = V ∧ (γ⁻¹ * V).trace = 0) :
    Function.Injective (metricSystemMatrix γ Hess).mulVec := by
  intro u v huv
  let w : (I dim) × (I dim) → ℝ := u - v
  let H : (Mat dim) := fun i j => w (i, j)
  have hw : metricSystemMatrix γ Hess *ᵥ w = 0 := by
    rw [show w = u - v from rfl, Matrix.mulVec_sub, huv, sub_self]
  have hrow (row : MetricSystemRow dim n) :
      (metricSystemMatrix γ Hess *ᵥ (fun ij => H ij.1 ij.2)) row = 0 := by
    change (metricSystemMatrix γ Hess *ᵥ w) row = 0
    rw [hw]
    rfl
  have hsymm : H.transpose = H := by
    ext i j
    exact sub_eq_zero.mp ((metricSystemMatrix_symmetry γ Hess H j i).symm.trans (hrow _))
  have htrace := (metricSystemMatrix_trace γ Hess H).symm.trans (hrow _)
  have hvalues a := (metricSystemMatrix_hessian γ Hess H a).symm.trans (hrow _)
  have hzero := symmetric_eq_zero_of_spanning_traces hγ hsymm htrace hspan hvalues
  funext ij
  exact sub_eq_zero.mp (congrArg (fun M : (Mat dim) => M ij.1 ij.2) hzero)

theorem gram_posDef_of_mulVec_injective {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] {A : Matrix r c ℝ} (h : Function.Injective A.mulVec) :
    (A.transpose * A).PosDef := by
  have hid : (1 : Matrix r r ℝ).PosDef := Matrix.PosDef.one
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
    hid.conjTranspose_mul_mul_same h

/-- The left inverse used at each center where the harmonic trace system
is injective. -/
theorem gram_left_inverse_of_det_ne_zero {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c] {A : Matrix r c ℝ} (h : (A.transpose * A).det ≠ 0) :
    ((A.transpose * A)⁻¹ * A.transpose) * A = 1 := by
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)]

theorem gram_left_inverse {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c] {A : Matrix r c ℝ} (h : Function.Injective A.mulVec) :
    ((A.transpose * A)⁻¹ * A.transpose) * A = 1 :=
  gram_left_inverse_of_det_ne_zero (gram_posDef_of_mulVec_injective h).det_pos.ne'

theorem contDiffOn_gram_entry {E r c : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype r] {U : Set E} {A : E → Matrix r c ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) (i j : c) :
    ContDiffOn ℝ ∞ (fun x => ((A x).transpose * A x) i j) U := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact ContDiffOn.sum fun k _ => (hA k i).mul (hA k j)

theorem contDiffOn_gram_leftInverse_entry {E r c : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype r] [Fintype c] [DecidableEq c]
    {U : Set E} {A : E → Matrix r c ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hdet : ∀ x ∈ U, ((A x).transpose * A x).det ≠ 0) (i : c) (j : r) :
    ContDiffOn ℝ ∞ (fun x => (((A x).transpose * A x)⁻¹ * (A x).transpose) i j) U := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact ContDiffOn.sum fun k _ =>
    (contDiffOn_inv_entry_of_entries (contDiffOn_gram_entry hA) hdet i k).mul (hA j k)

/-- Injectivity at every point of the compact undilated slice gives one
neighborhood of the dilation parameter on which the Gram matrix stays
invertible for the whole base. -/
theorem eventually_gram_det_ne_zero_on_compact
    {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]
    {K : Set (X dim)} (hK : IsCompact K) {U : Set (ℝ × (X dim))} (hU : IsOpen U)
    {A : ℝ × (X dim) → Matrix r c ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun q => A q i j) U)
    (hbase : ∀ y ∈ K, ((0 : ℝ), y) ∈ U ∧ Function.Injective (A (0, y)).mulVec) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K,
      (lam, y) ∈ U ∧ ((A (lam, y)).transpose * A (lam, y)).det ≠ 0 := by
  let D (p : ℝ × (X dim)) := ((A p).transpose * A p).det
  have hc : ContinuousOn D U := (contDiffOn_det_of_entries (contDiffOn_gram_entry hA)).continuousOn
  refine hK.eventually_forall_of_forall_eventually (P := fun lam y => (lam, y) ∈ U ∧ D (lam, y) ≠ 0) ?_
  intro y hy
  obtain ⟨h₀, hinj⟩ := hbase y hy
  have hn := hU.mem_nhds h₀
  have hD₀ : D (0, y) ≠ 0 := (gram_posDef_of_mulVec_injective hinj).det_pos.ne'
  have hp : {q | D q ≠ 0} ∈ 𝓝 ((0 : ℝ), y) :=
    (hc.continuousAt hn).preimage_mem_nhds (isOpen_ne.mem_nhds hD₀)
  filter_upwards [hn, hp] with q hq hD
  exact ⟨hq, hD⟩

end CalderonN
