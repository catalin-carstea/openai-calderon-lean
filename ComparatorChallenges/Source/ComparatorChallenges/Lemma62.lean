module

public import Proof.CalderonN.Coordinates
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

public section

open CalderonN MeasureTheory Metric Set
open scoped ContDiff

namespace CalderonPaper

/-- Lemma 6.2 of the pinned manuscript. The jet estimate is written in the
equivalent operator norm and multiplied by the positive factor `s^j`.
The bound on the order-`m` jet is supplied by the manuscript's `C^m` bound. -/
theorem lemma62 (dim m : ℕ) [NeZero dim] :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : X dim → ℝ) (U : Set (X dim)) (y : X dim)
        (s A : ℝ) (j : ℕ),

      -- Local smoothness, radius, and highest derivative bound.
      IsOpen U → ContDiffOn ℝ ∞ F U → closedBall y s ⊆ U →
      0 < s → s ≤ 1 → 0 ≤ A →
      (∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ m F x‖ ≤ A) →
      j < m →

      -- Scale-normalized lower derivative bound.
      s ^ j * ‖iteratedFDeriv ℝ j F y‖ ≤ C *
        (((s ^ dim)⁻¹) ^ ((1 : ℝ) / 2) *
          lpNorm F 2 (volume.restrict (ball y s)) + A * s ^ m) := by
  sorry

end CalderonPaper
