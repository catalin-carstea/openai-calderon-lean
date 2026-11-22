module

public import Proof.Manuscript.Lemma54
public import Mathlib.Tactic.NormNum

public section

open CalderonN CalderonN.FixedTube CalderonN.MovingSphere Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- At the initial member of the family, bound the actual squared density integral. -/
theorem lemma54_initialRadius_square (hn : 3 ≤ dim)
    {normal : I dim} {Ω W Z : Set (X dim)} (hΩ : IsOpen Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {G₁ G₂ : X dim × X dim → ℝ}
    (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
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
    {k : ℕ} {M : Fin (k + 1) → ℝ} {Cj : Fin 9 → ℝ}
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor M Cj)
    (hEstimate : UniformEstimate (interior (coordinateCylinder normal)) (ball (0 : X dim) 3)
      K ρ c₀ M Cj floor ε₀ C)
    (hData : UniformCylinderScaledGreenDataJets normal g₁ g₂ W (interior Z) G₁ G₂ E
      p ρ R ε tb (2 * dim + 8)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
        let Y := interior (coordinateCylinder normal)
        let χ := cylinderCutoff normal 4 tb
        let r := shrinkingRadius R p (conformalDepth normal 4) 1
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
          outputSq Y γ e (fun q => (χ q.1 : ℂ) * (ψ q : ℂ)) ≤ D ^ 2 := by
  obtain ⟨D, hD, h⟩ := lemma54 hn hΩ hside hg₁ hg₂ hG₁ hG₂ hE hp hρ hR hε htb hK
    hfloor hε₀ hC hdepth hCZ hNormal hRadius hSetup hEstimate hData
  refine ⟨D, hD, h.mono fun _ h hpos hSmall => ?_⟩
  obtain ⟨O, G, hO, hG, hSphere, hKnown, hDensity⟩ := h hpos 1 ⟨zero_lt_one, le_rfl⟩ hSmall
  exact ⟨O, G, hO, hG, hSphere, hKnown, (Real.sqrt_le_iff.mp hDensity).2⟩

end CalderonPaper
