module

public import Proof.Manuscript.Lemma63
public import Mathlib.Tactic.NormNum

public section

open CalderonN Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- On radii at most one, the superlinear bound gives a uniform linear bound. -/
theorem lemma63_linear (hn : 3 ≤ dim)
    {normal : I dim} {Ω W Z : Set (X dim)} (hΩ : IsOpen Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁₀ : g₁ 0 = 1) (hg₂₀ : g₂ 0 = 1)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : X dim × X dim → ℝ}
    (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {a : ℕ} {u₁ u₂ : Fin a → X dim → ℝ}
    (hu₁ : ∀ i, Harmonic Ω g₁ (u₁ i)) (hu₂ : ∀ i, Harmonic Ω g₂ (u₂ i))
    (hpair : ∀ i, EqOn (u₁ i) (u₂ i) W) (hspan : HessianSpanning g₁ u₁)
    {E : ℝ → X dim × X dim → X dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    {p : ℕ} (hp : 21 + dim ≤ p)
    {ρ R ε tb K c₀ floor ε₀ C : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (htb : 0 < tb) (hK : 0 < K) (hfloor : 1 ≤ floor) (hε₀ : ε ≤ ε₀) (hC : 0 ≤ C)
    (hdepth : ∀ y, conformalDepth normal 4 y ≤ 3 * tb → parabolicHeight normal y < 1 / 4)
    (hZ : IsCompact Z) (hCZ : coordinateCylinder normal ⊆ interior Z)
    (hZO : Z ⊆ ball (0 : X dim) 3)
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
    ∃ D ρ₀ : ℝ, 0 < D ∧ 0 < ρ₀ ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ δ ∈ Ioc (0 : ℝ) 1,
        let Y := interior (coordinateCylinder normal)
        let K := cylinderCore normal 4 tb
        let r := shrinkingRadius R p (conformalDepth normal 4) δ
        let γ := conformalReference (depthScale normal 4) g₁ lam
        let q₂ := dilatedMetric g₂ lam
        Small Y γ q₂ r ε →
        ∀ y ∈ K, r y < ρ₀ → r y ≤ 1 → smallJet γ q₂ y ≤ D * r y := by
  obtain ⟨D, ρ₀, hD, hρ₀, h⟩ := lemma63 hn hΩ hside hg₁ hg₂ hg₁₀ hg₂₀ hchart₁ hchart₂
    hG₁ hG₂ hmetric hgreen hu₁ hu₂ hpair hspan hE hp hρ hR hε htb hK hfloor hε₀ hC hdepth hZ hCZ hZO
    hNormal hRadius hSetup hEstimate hData
  refine ⟨D, ρ₀, hD, hρ₀, h.mono fun _ h hpos δ hδ hSmall y hy hSmallR hLe => ?_⟩
  let r := shrinkingRadius R p (conformalDepth normal 4) δ
  have hPositive : 0 < r y := shrinkingRadius_pos hR hδ.1 p _ y
  have hPower : (r y) ^ (3 / 2 : ℝ) ≤ r y := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hPositive hLe
        (by norm_num : (1 : ℝ) ≤ 3 / 2))
  exact (h hpos δ hδ hSmall y hy hSmallR).trans (mul_le_mul_of_nonneg_left hPower hD.le)

end CalderonPaper
