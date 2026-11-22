module

public import Proof.Manuscript.MovingTrace.SmoothProfileContribution
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2900000

open Set
open scoped ContDiff

namespace CalderonPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Removing extra transport terms preserves the desired remainder order
through every fixed finite joint derivative. -/
theorem compactPowerSeries_tail_jets
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (b : ℕ → E → ℂ) (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (R M N : ℕ) (hRM : R ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ q ∈ K, ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (fun q =>
        (∑ k ∈ Finset.range M, (h : ℂ)^k * b k q) -
          ∑ k ∈ Finset.range R, (h : ℂ)^k * b k q) q‖ ≤ C*h^R := by
  let I := Finset.Ico R M
  have hB (i : ℕ) (j : Fin (N+1)) : ∃ C ≥ 0, ∀ q ∈ K, ‖iteratedFDeriv ℝ j.val (b i) q‖ ≤ C := by
    have hC : ContinuousOn (fun q => ‖iteratedFDeriv ℝ j.val (b i) q‖) K := by
      intro q hq
      exact (((hb i).contDiffAt (hU.mem_nhds (hKU hq))).continuousAt_iteratedFDeriv
        (by simp : (j.val : ℕ∞ω) ≤ ∞)).norm.continuousWithinAt
    obtain ⟨C,hC'⟩ := hK.bddAbove_image hC
    exact ⟨max 0 C,le_max_left _ _,fun q hq => (hC' ⟨q,hq,rfl⟩).trans (le_max_right _ _)⟩
  choose B hB hBound using hB
  let C (i : ℕ) := ∑ j : Fin (N+1), B i j
  have hC (i : ℕ) : 0 ≤ C i := Finset.sum_nonneg (fun j _ => hB i j)
  refine ⟨∑ i ∈ I, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro h hh hh₁ q hq j hj
  let k : Fin (N+1) := ⟨j,Nat.lt_succ_of_le hj⟩
  have hEq : (fun q =>
        (∑ i ∈ Finset.range M, (h : ℂ)^i * b i q) - ∑ i ∈ Finset.range R, (h : ℂ)^i * b i q) =
      (fun q => ∑ i ∈ I, h^i • b i q) := by
    funext q
    have he := Finset.sum_range_add_sum_Ico (fun i => (h : ℂ)^i * b i q) hRM
    rw [← he,add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.real_smul,Complex.ofReal_pow]
  rw [hEq,iteratedFDeriv_fun_sum_apply]
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hS : ContDiffAt ℝ ∞ (b i) q := (hb i).contDiffAt (hU.mem_nhds (hKU hq))
    change ‖iteratedFDeriv ℝ j (h^i • b i) q‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (hS.of_le (by simp)),norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hh.le i),mul_comm (h^i)]
    exact mul_le_mul ((hBound i k q hq).trans
      (Finset.single_le_sum (fun l _ => hB i l) (Finset.mem_univ k)))
      (pow_le_pow_of_le_one hh.le hh₁ (Finset.mem_Ico.mp hi).1)
      (by positivity) (hC i)
  · intro i hi
    exact (((hb i).contDiffAt (hU.mem_nhds (hKU hq))).const_smul (h^i)).of_le (by simp)

end CalderonPaper
