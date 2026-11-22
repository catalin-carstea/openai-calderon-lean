module

public import Proof.CalderonN.InverseMetricBounds

import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ}

/-! The order-shift argument adapts the coordinate derivative bounds in
`Calderon/CoordinateH8FrechetRecovery.lean` to a germ in the selected chart. -/

theorem norm_iteratedFDeriv_coordDeriv_le {f : (X dim) → ℝ} {x : (X dim)}
    (hf : ContDiffAt ℝ ∞ f x) (i : (I dim)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (coordDeriv i f) x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  let A := ContinuousLinearMap.apply ℝ ℝ (axis i)
  have hA : ‖A‖ ≤ 1 := by
    refine A.opNorm_le_bound zero_le_one fun z => ?_
    simpa only [A, ContinuousLinearMap.apply_apply, norm_axis, mul_one, one_mul] using
      z.le_opNorm (axis i)
  change ‖iteratedFDeriv ℝ n (A ∘ fderiv ℝ f) x‖ ≤ _
  calc
    _ ≤ ‖A‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ :=
      A.norm_iteratedFDeriv_comp_left (hf.fderiv_right (m := ∞) (by simp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ :=
      mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_hessian_entry_le {f : (X dim) → ℝ} {x : (X dim)}
    (hf : ContDiffAt ℝ ∞ f x) (i j : (I dim)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => hessian f y i j) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 2) f x‖ := by
  have h := (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
      (g := fun _ : (X dim) => axis j)
  exact (norm_iteratedFDeriv_coordDeriv_le h i n).trans
    (norm_iteratedFDeriv_coordDeriv_le hf j (n + 1))

private theorem norm_iteratedFDeriv_iterate_coordDeriv_le {U : Set (X dim)} (hU : IsOpen U)
    {x : (X dim)} (hx : x ∈ U) (i : (I dim)) (j : ℕ) {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ ((coordDeriv i)^[j] f) U ∧
      ∀ n : ℕ, ‖iteratedFDeriv ℝ n ((coordDeriv i)^[j] f) x‖ ≤
        ‖iteratedFDeriv ℝ (n + j) f x‖ := by
  induction j with
  | zero => exact ⟨hf, fun _ => le_rfl⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨contDiffOn_coordDeriv ih.1 hU i, fun n => ?_⟩
    calc
      _ ≤ ‖iteratedFDeriv ℝ (n + 1) ((coordDeriv i)^[j] f) x‖ :=
        norm_iteratedFDeriv_coordDeriv_le (ih.1.contDiffAt (hU.mem_nhds hx)) i n
      _ ≤ ‖iteratedFDeriv ℝ (n + 1 + j) f x‖ := ih.2 (n + 1)
      _ = _ := by rw [Nat.add_assoc, Nat.add_comm 1 j]

theorem norm_chartPartial_le {U : Set (X dim)} (hU : IsOpen U)
    {x : X dim} (hx : x ∈ U) {f : X dim → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (a : I dim → ℕ) :
    ‖chartPartial a f x‖ ≤ ‖iteratedFDeriv ℝ (∑ i, a i) f x‖ := by
  let applyWord (w : List (I dim)) :=
    w.foldr (fun i u => (coordDeriv (E := ℝ) i)^[a i] u) f
  have hword (w : List (I dim)) : ContDiffOn ℝ ∞ (applyWord w) U ∧
      ∀ k, ‖iteratedFDeriv ℝ k (applyWord w) x‖ ≤
        ‖iteratedFDeriv ℝ (k + (w.map a).sum) f x‖ := by
    induction w with
    | nil => exact ⟨hf, fun k => by rfl⟩
    | cons i w ih =>
      obtain ⟨hs, hle⟩ := norm_iteratedFDeriv_iterate_coordDeriv_le hU hx i (a i) ih.1
      refine ⟨hs, fun k => ?_⟩
      change ‖iteratedFDeriv ℝ k ((coordDeriv i)^[a i] (applyWord w)) x‖ ≤
        ‖iteratedFDeriv ℝ (k + (a i + (w.map a).sum)) f x‖
      rw [← Nat.add_assoc]
      exact (hle k).trans (ih.2 (k + a i))
  let w := List.ofFn (fun i : I dim => i)
  have hw : w.map a = List.ofFn a := by simp [w, Function.comp_def]
  have hD : w.map (fun i => (coordDeriv (E := ℝ) i)^[a i]) =
      List.ofFn (fun i : I dim => (coordDeriv (E := ℝ) i)^[a i]) := by
    simp [w, Function.comp_def]
  have h := (hword w).2 0
  rw [hw, List.sum_ofFn, zero_add, norm_iteratedFDeriv_zero] at h
  unfold chartPartial
  rw [← hD, List.foldr_map]
  exact h

end CalderonN
