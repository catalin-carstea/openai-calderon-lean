module

public import Proof.CalderonN.ParametricBallStrongSolution

import Proof.CalderonN.InteriorFluxEnergy
import Mathlib.Tactic

public section

noncomputable section

open Set Metric Filter CalderonN CalderonN.BallDirichlet
open scoped ContDiff Topology

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n]

/-- An arbitrary number of nested cutoff commutators can be fitted
inside the fixed unit ball, with positive gaps between the cutoffs. -/
theorem exists_nestedBallCutoffs :
    ∃ χ : ℕ → SmoothData n,
      (∀ j, HasCompactSupport (χ j).1) ∧
      (∀ j, tsupport (χ j).1 ⊆ ball (0 : X n) (1/2)) ∧
      (∀ j, (χ j).1 (0 : X n) = 1) ∧
      ∀ j, ∀ x ∈ tsupport (χ j).1, (χ (j+1)).1 =ᶠ[𝓝 x] fun _ => 1 := by
  let R (j : ℕ) : ℝ := 1/2 - 1/(4*(j+1 : ℕ))
  have hDen (j : ℕ) : 0 < (4 * (j+1 : ℕ) : ℝ) := by positivity
  have hR (j : ℕ) : 0 ≤ R j := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    dsimp only [R]
    have h : (1:ℝ) / (4 * (↑(j+1) : ℝ)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      push_cast
      linarith
    linarith
  have hRtop (j : ℕ) : R j < 1/2 := sub_lt_self _ (div_pos one_pos (hDen j))
  have hInc (j : ℕ) : R j < R (j+1) := by
    dsimp only [R]
    apply sub_lt_sub_left
    apply div_lt_div_of_pos_left one_pos (hDen j)
    push_cast
    linarith
  have hExist (j : ℕ) := CalderonN.Elliptic.exists_plateau_cutoff
    (isOpen_ball : IsOpen (ball (0 : X n) (R (j+1))))
    (isCompact_closedBall (0 : X n) (R j)) (closedBall_subset_ball (hInc j))
  choose χ hχ hc hsub hOne using hExist
  refine ⟨fun j => ⟨χ j,hχ j⟩, hc, fun j => (hsub j).trans (ball_subset_ball (hRtop _).le),
    fun j => (hOne j 0 (mem_closedBall_self (hR j))).eq_of_nhds,?_⟩
  exact fun j x hx => hOne (j+1) x (ball_subset_closedBall (hsub j hx))

end CalderonPaper.LowerGreen

end
