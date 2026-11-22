module

public import Proof.CalderonN.Chart

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

open Set
open scoped BigOperators ContDiff

namespace CalderonN

variable {n : ℕ}

/-! These local smoothness proofs adapt `Calderon/MetricSmooth.lean`
from the earlier Calderón formalization to the open chart. -/

theorem contDiffOn_det_of_entries
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    [DecidableEq J] {V : Set E} {g : E → Matrix J J ℝ}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) V) :
    ContDiffOn ℝ ∞ (fun x => (g x).det) V := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun j _ => hg (σ j) j)

theorem contDiffOn_inv_entry_of_entries
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    [DecidableEq J] {V : Set E} {g : E → Matrix J J ℝ}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) V)
    (hdet : ∀ x ∈ V, (g x).det ≠ 0) (i j : J) :
    ContDiffOn ℝ ∞ (fun x => (g x)⁻¹ i j) V := by
  have hadj : ContDiffOn ℝ ∞ (fun x => (g x).adjugate i j) V := by
    simp_rw [Matrix.adjugate_apply]
    apply contDiffOn_det_of_entries (g := fun x => (g x).updateRow j (Pi.single i 1))
    intro k l
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateRow_self]
      exact contDiffOn_const
    · simpa only [Matrix.updateRow_apply, hk, ite_false] using hg k l
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ((contDiffOn_det_of_entries hg).inv hdet).mul hadj

theorem contDiffOn_metric_inv_entry {Ω : Set (X n)} {g : (MetricField n)}
    (hg : SmoothMetric Ω g) (i j : (I n)) :
    ContDiffOn ℝ ∞ (fun x => (g x)⁻¹ i j) Ω :=
  contDiffOn_inv_entry_of_entries hg.1 (fun x hx => (hg.2 x hx).det_pos.ne') i j

theorem contDiffOn_metric_volume {Ω : Set (X n)} {g : (MetricField n)} (hg : SmoothMetric Ω g) :
    ContDiffOn ℝ ∞ (fun x => Real.sqrt (g x).det) Ω :=
  (contDiffOn_det_of_entries hg.1).sqrt (fun x hx => (hg.2 x hx).det_pos.ne')

theorem contDiffOn_coordDeriv {Ω : Set (X n)} {f : (X n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hΩ : IsOpen Ω) (i : (I n)) :
    ContDiffOn ℝ ∞ (coordDeriv i f) Ω :=
  (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_chartPartial {Ω : Set (X n)} (hΩ : IsOpen Ω) {f : X n → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (a : I n → ℕ) :
    ContDiffOn ℝ ∞ (chartPartial a f) Ω := by
  have hiter (i : I n) (k : ℕ) {u : X n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) :
      ContDiffOn ℝ ∞ ((coordDeriv i)^[k] u) Ω := by
    induction k with
    | zero => exact hu
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact contDiffOn_coordDeriv ih hΩ i
  unfold chartPartial
  have hfold (l : List (I n)) :
      ContDiffOn ℝ ∞ ((l.map (fun i => (coordDeriv i)^[a i])).foldr (fun D u => D u) f) Ω := by
    induction l with
    | nil => exact hf
    | cons i l ih => exact hiter i (a i) ih
  simpa only [List.map_ofFn, Function.comp_id] using hfold (List.ofFn id)

end CalderonN
