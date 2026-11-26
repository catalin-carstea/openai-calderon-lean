module

import Mathlib.Tactic
public import Proof.CalderonN.ConformalScaledGreenDataJets
public import Proof.CalderonN.ConformalCylinderAgreement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Proof.CalderonN.ActualMovingTraceAdjoint
public import Proof.CalderonN.MovingGreenFluxDensity

public section

open CalderonN CalderonN.FixedTube CalderonN.MovingSphere Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Lemma 5.4 of the pinned manuscript. The exact conormal density of
the continued Green kernel on the same moving spheres is uniformly
bounded after multiplication by the fixed base cutoff. -/
theorem lemma54 (hn : 3 ≤ dim)
    {normal : I dim} {Ω W Z : Set (X dim)} (hΩ : IsOpen Ω)
    (hside : ContainsAlignedSide normal Ω W)

    -- Metric and Green data on the common side.
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {G₁ G₂ : X dim × X dim → ℝ}
    (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)

    -- Normal coordinates, radius, and cutoff scales.
    {E : ℝ → X dim × X dim → X dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    {p : ℕ} (hp : 21 + dim ≤ p)
    {ρ R ε tb K c₀ floor ε₀ C : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (htb : 0 < tb) (hK : 0 < K) (hfloor : 1 ≤ floor) (hε₀ : ε ≤ ε₀) (hC : 0 ≤ C)
    (hdepth : ∀ y, conformalDepth normal 4 y ≤ 3 * tb → parabolicHeight normal y < 1 / 4)
    (hCZ : coordinateCylinder normal ⊆ interior Z)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : X dim) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Z,
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ / 2)

    -- Uniform angular and continued Green data.
    {k : ℕ} {M : Fin (k + 1) → ℝ} {Cj : Fin 9 → ℝ}
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor M Cj)
    (hEstimate : UniformEstimate (interior (coordinateCylinder normal)) (ball (0 : X dim) 3)
      K ρ c₀ M Cj floor ε₀ C)
    (hData : UniformCylinderScaledGreenDataJets normal g₁ g₂ W (interior Z) G₁ G₂ E
      p ρ R ε tb (2 * dim + 8)) :

    -- One flux bound for all sufficiently small positive dilations.
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ δ ∈ Ioc (0 : ℝ) 1,
        let Y := interior (coordinateCylinder normal)
        let χ := cylinderCutoff normal 4 tb
        let r := shrinkingRadius R p (conformalDepth normal 4) δ
        let γ := conformalReference (depthScale normal 4) g₁ lam
        let q₁ := dilatedMetric g₁ lam
        let q₂ := dilatedMetric g₂ lam
        let e := fun y : X dim => smoothMetricFrame (γ y)
        Small Y γ q₂ r ε →
        ∃ (O : Set (X dim × X dim)) (G : X dim × X dim → ℝ),
          IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
          (∀ y ∈ Y, ∀ w : ↥(standardSphere dim), (endpoint (E lam) r (y, frameVector e y w), y) ∈ O) ∧
          EqOn G (dilatedInitialGreen W G₁ G₂ lam)
            (lowerNormalSeed normal (normalPairDomain (interior Z) γ ρ (E lam))) ∧
          let ψ := movingGreenFluxDensity γ q₁ (E lam) e r G
          Real.sqrt (outputSq Y γ e (fun q => (χ q.1 : ℂ) * (ψ q : ℂ))) ≤ D := by
  sorry

end CalderonPaper
