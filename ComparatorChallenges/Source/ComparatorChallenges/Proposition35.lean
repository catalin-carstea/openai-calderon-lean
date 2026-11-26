module

public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.GreenDilation
public import Proof.CalderonN.FixedTube.Initialization

public section

open Set Filter
open scoped Topology
open CalderonN CalderonN.FixedTube

namespace CalderonPaper

/-- Proposition 3.5. The fixed scale and derivative order are chosen before
the neighborhoods and uniform bounds for the small spatial dilations. -/
theorem proposition35
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (normal : I n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsAlignedSide normal Ω W)

    -- Common-side metric and Green data.
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))

    -- Fixed scales and derivative order.
    {B d η : ℝ} (hB : 0 < B) (hd : 0 < d) (hη : 0 < η) (m : ℕ) :
    ∃ (U V : Set ((X n) × (X n))) (C : ℝ),
      IsOpen U ∧ IsOpen V ∧ fixedSeparationSet B d ⊆ V ∧ closure V ⊆ U ∧
      IsCompact (closure V) ∧ 0 ≤ C ∧

      -- Continuation for small positive dilations.
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
        U ⊆ OffDiagonal {x | lam • x ∈ Ω} ∧
        ∃ G : (X n) × (X n) → ℝ,
          ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) U G ∧
          EqOn G (dilatedGreen G₁ lam) {z ∈ U | lam • z.2 ∈ W} ∧
          EqOn G (dilatedGreen G₂ lam) {z ∈ U | lam • z.1 ∈ W} ∧
          EqOn G (dilatedGreen G₁ lam) {z ∈ U | z.2 normal < -η} ∧
          EqOn G (dilatedGreen G₂ lam) {z ∈ U | z.1 normal < -η} ∧
          ∀ k ≤ m, ∀ z ∈ V, ‖iteratedFDeriv ℝ k G z‖ ≤ C := by
  sorry

end CalderonPaper
