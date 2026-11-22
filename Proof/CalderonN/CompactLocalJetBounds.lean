module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

import Mathlib.Tactic

/-! A finite jet envelope on a compact set only needs smoothness at each
of its points. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
namespace CalderonN

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem exists_uniform_local_finite_jet_bound {J : Set P} (hJ : IsCompact J)
    {f : P → Q} (hf : ∀ x ∈ J, ContDiffAt ℝ ∞ f x) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ J, ∀ n ≤ N, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  choose B hB using fun k : Fin (N+1) => hJ.exists_bound_of_continuousOn
    (fun x hx => ((hf x hx).continuousAt_iteratedFDeriv (k:=k.val) (by simp)).continuousWithinAt)
  let C : ℝ := 1+∑ k, |B k|
  refine ⟨C,le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _),?_⟩
  intro x hx n hn
  let i : Fin (N+1) := ⟨n,by omega⟩
  exact (hB i x hx).trans ((le_abs_self _).trans
    ((Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1))))

end CalderonN
