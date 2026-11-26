module

public import Proof.CalderonN.ModelOutputLimits

public section

open CalderonN Set
open scoped ContDiff

namespace CalderonPaper

/-- Lemma 5.2 of the pinned manuscript. The two squared norms are for the
closed raising and lowering operators on the actual compactly supported
sphere test, with no angular truncation. -/
theorem lemma52 {dim : ℕ} [NeZero dim] (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hsub : Y ⊆ Ω)
    {K c₀ : ℝ} (hK : 0 < K) (hc₀ : 0 < c₀)
    {m : ℕ} (hm : 2 ≤ m) (M : Fin (m + 1) → ℝ) (Cj : Fin 9 → ℝ) :

    -- The floor and estimate constant precede the choice of metric, frame, and radius.
    ∃ floor c : ℝ, 1 ≤ floor ∧ 0 < c ∧
      ∀ (g : MetricField dim) (e : Frame dim), Elliptic Ω K g →
        (∀ (j : Fin (m + 1)) i l, ∀ y ∈ Ω,
          ‖iteratedFDeriv ℝ j.val (fun x => g x i l) y‖ ≤ M j) →
        (∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Ω) →
        (∀ y ∈ Ω, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) →

        -- Apply the estimate to each admitted radius and test field.
        ∀ (r : X dim → ℝ), Profile Y g e r floor c₀ Cj →
          ∀ φ : Field dim, Test Y g e φ →
            ∃ (E : HarmonicTestExpansion Y g e φ) (D : AngularModelData E r),
              c * energySq Y g e r φ ≤ D.raisingSquare - D.loweringSquare := by
  sorry

end CalderonPaper
