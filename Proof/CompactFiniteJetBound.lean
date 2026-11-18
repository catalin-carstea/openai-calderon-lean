import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- A common finite-jet bound on a compact set for a fixed smooth function.
    Applications to universal finite-dimensional formulas preserve uniformity
    over actual fields only after the input set and its bounds are explicit. -/
theorem exists_finite_jet_bound_on_compact
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : P → V) (K : Set P) (hK : IsCompact K)
    (hF : ∀ p ∈ K,ContDiffAt ℝ ∞ F p) (N : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ n : ℕ,n ≤ N → ∀ p ∈ K,‖iteratedFDeriv ℝ n F p‖ ≤ C := by
  have hEach (n : Fin (N+1)) : ∃ C : ℝ,∀ p ∈ K,‖iteratedFDeriv ℝ n.val F p‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro p hp
    exact ((hF p hp).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
  choose C hC using hEach
  let B := 1+∑ n : Fin (N+1),max (C n) 0
  have hSum : 0 ≤ ∑ n : Fin (N+1),max (C n) 0 := Finset.sum_nonneg (fun n _ => le_max_right _ _)
  refine ⟨B,by dsimp only [B];linarith,?_⟩
  intro n hn p hp
  let j : Fin (N+1) := ⟨n,by omega⟩
  have hTerm : max (C j) 0 ≤ ∑ n : Fin (N+1),max (C n) 0 :=
    Finset.single_le_sum (fun n _ => le_max_right _ _) (Finset.mem_univ j)
  exact (hC j p hp).trans ((le_max_left _ _).trans (by dsimp only [B];linarith only [hTerm]))

end ShrinkingSpheres
