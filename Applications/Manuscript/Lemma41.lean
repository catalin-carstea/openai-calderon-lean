module

public import Proof.Manuscript.Lemma41

public section

open Set CalderonN

namespace CalderonPaper

/-- The amplitude can be chosen after an arbitrary fixed exponent and before
the dilation and shrinking parameters are selected. -/
theorem lemma41_radiusBudget
    {n : ℕ} [NeZero n] (normal : I n)
    {Ω : Set (X n)} (hΩ : IsOpen Ω) (h0 : (0 : X n) ∈ Ω)
    {g : MetricField n} (hg : SmoothMetric Ω g) (hg0 : g 0 = 1)
    (p : ℕ) (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    ∃ L > 0, ∃ lam₀ > 0, ∃ R > 0,
      ∀ lam ∈ Ioo (0 : ℝ) lam₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ coordinateCylinder normal,
        let γ := conformalReference (depthScale normal L) g lam
        let r := shrinkingRadius R p (conformalDepth normal L) δ
        r y * (beta γ r y) ^ 2 ≤ ε := by
  obtain ⟨L, hL, c, hc, C, ⟨lam₀, hlam₀, hprofile, hsmall⟩, hshape⟩ :=
    lemma41 normal hΩ h0 hg hg0
  obtain ⟨R₀, hR₀, hbound⟩ := hsmall p hp ε hε
  exact ⟨L, hL, lam₀, hlam₀, R₀ / 2, half_pos hR₀,
    hbound (R₀ / 2) ⟨half_pos hR₀, half_lt_self hR₀⟩⟩

end CalderonPaper
