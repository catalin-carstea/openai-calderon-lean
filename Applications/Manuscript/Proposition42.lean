module

public import Proof.Manuscript.Proposition42

public section

open Set Filter Metric CalderonN
open CalderonN.FixedTube CalderonN.MovingSphere
open scoped ContDiff Topology

namespace CalderonPaper

/-- Choose the compact dilation and radius witnesses used by the transfer
construction, then continue the same lower kernel around every normal
sphere at the selected shrinking parameter. -/
theorem proposition42_continueSelectedSpheres
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (normal : I n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W)) :
    ∃ (p : ℕ) (ε R ρ lam₀ : ℝ) (E : ℝ → (X n) × (X n) → (X n)),
      2 ≤ p ∧ 0 < ε ∧ 0 < R ∧ 0 < ρ ∧ 0 < lam₀ ∧
      (∀ lam ∈ Icc (-lam₀) lam₀,
        NormalCoordinates (closedBall (0 : X n) (5/2)) (ball (0 : X n) 3)
          (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ)) ∧
      (∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ coordinateCylinder normal,
        shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ/2) ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
        let Y := coordinateCylinder normal
        let γ := conformalReference (depthScale normal 4) g₁ lam
        let r := shrinkingRadius R p (conformalDepth normal 4)
        let q₁ := dilatedMetric g₁ lam
        let q₂ := dilatedMetric g₂ lam
        ∀ δ ∈ Ioc (0 : ℝ) 1, (∀ y ∈ Y, smallJet γ q₂ y ≤ ε * r δ y) →
          ∃ (O : Set ((X n) × (X n))) (G : (X n) × (X n) → ℝ),
            IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
            ∀ w ∈ bundle Y γ, (endpoint (E lam) (r δ) w, w.1) ∈ O := by
  obtain ⟨ρ, tb, lam₀, E, hρ, _, hlam₀, _, _, hNormal, pmin, εmax, Rmax, hpmin, hεpos, hRpos, hcont⟩ :=
    proposition42 hn normal hΩ hW hWΩ hside hg₁ hg₂ h₁ h₂ hG₁ hG₂ hmetric hgreen
  let ε := εmax pmin
  have hε : ε ∈ Ioc (0 : ℝ) (εmax pmin) := ⟨hεpos pmin le_rfl, le_rfl⟩
  let R := Rmax pmin ε
  have hR : R ∈ Ioc (0 : ℝ) (Rmax pmin ε) := ⟨hRpos pmin le_rfl ε hε, le_rfl⟩
  obtain ⟨d, C, hd, _, hRadius, hbuild⟩ := hcont pmin le_rfl ε hε R hR
  refine ⟨pmin, ε, R, ρ, lam₀, E, hpmin, hε.1, hR.1, hρ, hlam₀, hNormal, hRadius, ?_⟩
  filter_upwards [hbuild] with lam hlam hpos
  obtain ⟨_, _, O₀, F, _, _, _, _, hspheres⟩ := hlam hpos
  dsimp only
  intro δ hδ hsmall
  obtain ⟨O, G, hO, hG, _, _, hinc, _, _⟩ := hspheres δ hδ (fun y hy => hsmall y (interior_subset hy))
  exact ⟨O, G, hO, hG, hinc δ ⟨le_rfl, hδ.2⟩⟩

end CalderonPaper
