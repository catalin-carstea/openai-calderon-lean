module

public import Proof.CalderonN.CylinderCutoff
public import Proof.CalderonN.NormalInverse
public import Proof.CalderonN.Radius
public import Proof.CalderonN.MovingSphere.RadiusSeed

public section

open Set Filter Metric CalderonN
open CalderonN.FixedTube CalderonN.MovingSphere
open scoped ContDiff Topology

namespace CalderonPaper

/-- Proposition 4.2. The same continued kernel solves the two dilated
equations on an open neighborhood of the normal spheres and retains the
prescribed lower and positive-separation seeds. -/
theorem proposition42
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (normal : I n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsAlignedSide normal Ω W)

    -- Common-side metric and Green data.
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W)) :

    -- Fixed cylinder and conformal reference.
    let Y := coordinateCylinder normal
    let Z := closedBall (0 : X n) (5 / 2)
    let t := conformalDepth normal 4
    let γ := conformalReference (depthScale normal 4) g₁

    -- Normal-coordinate family, followed by the continuation data.
    ∃ (ρ tb lam₀ : ℝ) (E : ℝ → (X n) × (X n) → (X n)),
      0 < ρ ∧ 0 < tb ∧ 0 < lam₀ ∧ ContDiff ℝ ∞ (fun q : ℝ × ((X n) × (X n)) => E q.1 q.2) ∧
      (∀ y, t y ≤ 3 * tb → parabolicHeight normal y < 1 / 4) ∧
      (∀ lam ∈ Icc (-lam₀) lam₀, NormalCoordinates Z (ball (0 : X n) 3)
        (γ lam) (E lam) (fun _ => ρ)) ∧
      ∃ (pmin : ℕ) (εmax : ℕ → ℝ) (Rmax : ℕ → ℝ → ℝ),
        2 ≤ pmin ∧ (∀ p ≥ pmin, 0 < εmax p) ∧
        (∀ p ≥ pmin, ∀ ε ∈ Ioc (0 : ℝ) (εmax p), 0 < Rmax p ε) ∧
        ∀ p ≥ pmin, ∀ ε ∈ Ioc (0 : ℝ) (εmax p), ∀ R ∈ Ioc (0 : ℝ) (Rmax p ε),
          let r := shrinkingRadius R p t
          ∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧
            (∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y, r a y ≤ ρ/2) ∧
            ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
            let N := normalPairDomain (interior Z) (γ lam) ρ (E lam)
            let q₁ := dilatedMetric g₁ lam
            let q₂ := dilatedMetric g₂ lam
            ball (0 : X n) 3 ⊆ {y | lam • y ∈ Ω} ∧
            (∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y, r a y < ρ ∧ r a y * (beta (γ lam) (r a) y)^2 ≤ ε) ∧
            ∃ (O₀ : Set ((X n) × (X n))) (F : (X n) × (X n) → ℝ),
              IsOpen O₀ ∧ fixedSeparationSet 4 (d/2) ⊆ O₀ ∧
              ProductSolutionOn q₁ q₂ O₀ F ∧ (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ C) ∧
              (∀ δ ∈ Ioc (0 : ℝ) 1, (∀ y ∈ interior Y, smallJet (γ lam) q₂ y ≤ ε * r δ y) →
                ∃ (O : Set ((X n) × (X n))) (G : (X n) × (X n) → ℝ),
                  IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
                  lowerNormalSeed normal N ⊆ O ∧
                  EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) ∧
                  (∀ a ∈ Icc δ 1, ∀ w ∈ bundle Y (γ lam), (endpoint (E lam) (r a) w, w.1) ∈ O) ∧
                  (∀ w ∈ bundle Y (γ lam), tb < t w.1 →
                    let q := (endpoint (E lam) (r δ) w, w.1)
                    q ∈ fixedSeparationSet 3 d ∧ G =ᶠ[𝓝 q] F) ∧
                  ∀ w ∈ bundle Y (γ lam), w.1 normal < -(1/4 : ℝ) →
                    let q := (endpoint (E lam) (r δ) w, w.1)
                    ‖q.1‖ ≤ 3 ∧ ‖q.2‖ ≤ 3 ∧ G =ᶠ[𝓝 q] dilatedGreen G₁ lam) := by
  sorry

end CalderonPaper
