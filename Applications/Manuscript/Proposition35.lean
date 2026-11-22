module

public import Proof.Manuscript.Proposition35

public section

open Set Filter CalderonN CalderonN.FixedTube
open scoped Topology

namespace CalderonPaper

/-- A fixed separated range inherits the two original Green kernels on
their known cap arms, and the first kernel below the prescribed slice. -/
theorem proposition35_prescribedGreen
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (normal : I n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {B d η : ℝ} (hB : 0 < B) (hd : 0 < d) (hη : 0 < η) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∃ (U : Set ((X n) × (X n))) (G : (X n) × (X n) → ℝ),
        IsOpen U ∧ fixedSeparationSet B d ⊆ U ∧
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) U G ∧
        EqOn G (dilatedGreen G₁ lam) {z ∈ fixedSeparationSet B d | lam • z.2 ∈ W} ∧
        EqOn G (dilatedGreen G₂ lam) {z ∈ fixedSeparationSet B d | lam • z.1 ∈ W} ∧
        EqOn G (dilatedGreen G₁ lam) {z ∈ fixedSeparationSet B d | z.2 normal < -η} := by
  obtain ⟨U, V, C, hU, hV, hset, hVU, _, _, hdata⟩ :=
    proposition35 hn normal hΩ hW hWΩ hside hg₁ hg₂ h₁ h₂ hG₁ hG₂ hmetric hgreen hB hd hη 0
  filter_upwards [hdata] with lam hlam hpos
  obtain ⟨_, G, hG, hcapLeft, hcapRight, hleft, _, _⟩ := hlam hpos
  have htargetU := hset.trans (subset_closure.trans hVU)
  exact ⟨U, G, hU, htargetU, hG,
    fun _ hz => hcapLeft ⟨htargetU hz.1, hz.2⟩,
    fun _ hz => hcapRight ⟨htargetU hz.1, hz.2⟩,
    fun _ hz => hleft ⟨htargetU hz.1, hz.2⟩⟩

end CalderonPaper
