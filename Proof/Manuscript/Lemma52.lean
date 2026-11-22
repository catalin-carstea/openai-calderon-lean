module

public import Proof.CalderonN.ModelOutputLimits

import Proof.CalderonN.SmoothModelCoercivity

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
    ∃ floor c : ℝ, 1 ≤ floor ∧ 0 < c ∧
      ∀ (g : MetricField dim) (e : Frame dim), Elliptic Ω K g →
        (∀ (j : Fin (m + 1)) i l, ∀ y ∈ Ω,
          ‖iteratedFDeriv ℝ j.val (fun x => g x i l) y‖ ≤ M j) →
        (∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Ω) →
        (∀ y ∈ Ω, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) →
        ∀ (r : X dim → ℝ), Profile Y g e r floor c₀ Cj →
          ∀ φ : Field dim, Test Y g e φ →
            ∃ (E : HarmonicTestExpansion Y g e φ) (D : AngularModelData E r),
              c * energySq Y g e r φ ≤ D.raisingSquare - D.loweringSquare := by
  refine ⟨backgroundCoercivityFloor dim hm K M c₀, backgroundModeCoercivityConstant c₀,
    backgroundCoercivityFloor_ge_one dim hm K M c₀, backgroundModeCoercivityConstant_pos c₀ hc₀, ?_⟩
  intro g e hElliptic hJet he hFrame r hr φ hφ
  have hBg : Background Ω K M g g g e := by
    refine ⟨hElliptic, hElliptic, hElliptic, ?_, ?_, ?_, he, hFrame⟩
    · exact fun y _ => ⟨1, zero_lt_one, (one_smul ℝ (g y)).symm⟩
    · intro g' hg'
      have hEq : g' = g := by simpa using hg'
      subst g'
      exact hJet
    · intro y _ i
      simpa [drift] using hK.le
  exact hBg.exists_coercive_smooth_model hn hY hΩ hsub hK hm hr hc₀ le_rfl hφ

end CalderonPaper
