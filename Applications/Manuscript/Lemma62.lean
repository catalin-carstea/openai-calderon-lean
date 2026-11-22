module

public import Proof.Manuscript.Lemma62

public section

open CalderonN MeasureTheory Metric Set
open scoped ContDiff

namespace CalderonPaper

/-- At unit scale the interpolation estimate bounds the value at the
center by the local quadratic mean and the highest derivative. -/
theorem lemma62_unitBall_value (dim m : ℕ) [NeZero dim] :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : X dim → ℝ) (U : Set (X dim)) (y : X dim) (A : ℝ),
      IsOpen U → ContDiffOn ℝ ∞ F U → closedBall y 1 ⊆ U → 0 ≤ A →
      (∀ x ∈ closedBall y 1, ‖iteratedFDeriv ℝ (m + 1) F x‖ ≤ A) →
      |F y| ≤ C * (lpNorm F 2 (volume.restrict (ball y 1)) + A) := by
  obtain ⟨C, hC, h⟩ := lemma62 dim (m + 1)
  refine ⟨C, hC, ?_⟩
  intro F U y A hU hF hBall hA hD
  simpa using h F U y 1 A 0 hU hF hBall zero_lt_one le_rfl hA hD (Nat.zero_lt_succ m)

end CalderonPaper
