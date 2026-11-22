module

public import Proof.Manuscript.Lemma52

public section

open CalderonN Set
open scoped ContDiff

namespace CalderonPaper

/-- Use the model estimate to bound the loss from lowering and retain a
strict gain for every test of positive physical energy. -/
theorem lemma52_raising_strict {dim : ℕ} [NeZero dim] (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hsub : Y ⊆ Ω)
    {K c₀ : ℝ} (hK : 0 < K) (hc₀ : 0 < c₀)
    {m : ℕ} (hm : 2 ≤ m) (M : Fin (m + 1) → ℝ) (Cj : Fin 9 → ℝ) :
    ∃ floor : ℝ, 1 ≤ floor ∧
      ∀ (g : MetricField dim) (e : Frame dim), Elliptic Ω K g →
        (∀ (j : Fin (m + 1)) i l, ∀ y ∈ Ω,
          ‖iteratedFDeriv ℝ j.val (fun x => g x i l) y‖ ≤ M j) →
        (∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Ω) →
        (∀ y ∈ Ω, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) →
        ∀ (r : X dim → ℝ), Profile Y g e r floor c₀ Cj →
          ∀ φ : Field dim, Test Y g e φ → 0 < energySq Y g e r φ →
            ∃ (E : HarmonicTestExpansion Y g e φ) (D : AngularModelData E r),
              D.loweringSquare < D.raisingSquare := by
  obtain ⟨floor, c, hfloor, hc, h⟩ :=
    lemma52 hn hY hΩ hsub hK hc₀ hm M Cj
  refine ⟨floor, hfloor, ?_⟩
  intro g e hElliptic hJet he hFrame r hr φ hφ hEnergy
  obtain ⟨E, D, hD⟩ := h g e hElliptic hJet he hFrame r hr φ hφ
  exact ⟨E, D, sub_pos.mp ((mul_pos hc hEnergy).trans_le hD)⟩

end CalderonPaper
