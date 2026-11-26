module

import Mathlib.Tactic
public import Proof.CalderonN.ConformalScaledGreenDataJets
public import Proof.CalderonN.ConformalCylinderAgreement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

public section

open CalderonN Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Lemma 6.1 of the pinned manuscript on the fixed normalized conformal
cylinder, for the entire paired harmonic family and the same spheres,
cutoff and continued Green data as in Sections 4 and 5. -/
theorem lemma61 (hn : 3 ≤ dim)
    {normal : I dim} {Ω W Z : Set (X dim)} (hΩ : IsOpen Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁₀ : g₁ 0 = 1) (hg₂₀ : g₂ 0 = 1)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : X dim × X dim → ℝ}
    (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))

    -- Paired harmonic family.
    {a : ℕ} {u₁ u₂ : Fin a → X dim → ℝ}
    (hu₁ : ∀ i, Harmonic Ω g₁ (u₁ i)) (hu₂ : ∀ i, Harmonic Ω g₂ (u₂ i))
    (hpair : ∀ i, EqOn (u₁ i) (u₂ i) W)

    -- Normal coordinates, radius, and cutoff scales.
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

    -- Uniform angular and continued Green data.
    {k : ℕ} {M : Fin (k + 1) → ℝ} {Cj : Fin 9 → ℝ}
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor M Cj)
    (hEstimate : UniformEstimate (interior (coordinateCylinder normal)) (ball (0 : X dim) 3)
      K ρ c₀ M Cj floor ε₀ C)
    (hData : UniformCylinderScaledGreenDataJets normal g₁ g₂ W (interior Z) G₁ G₂ E
      p ρ R ε tb (2 * dim + 8)) :

    -- One moment bound for every member of the family.
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ δ ∈ Ioc (0 : ℝ) 1,
        let Y := interior (coordinateCylinder normal)
        let χ := cylinderCutoff normal 4 tb
        let r := shrinkingRadius R p (conformalDepth normal 4) δ
        Small Y (conformalReference (depthScale normal 4) g₁ lam) (dilatedMetric g₂ lam) r ε →
        ∀ i : Fin a,
          let v₁ := renormalizedHarmonic (u₁ i 0) (fderiv ℝ (u₁ i) 0) (u₁ i) lam
          let v₂ := renormalizedHarmonic (u₁ i 0) (fderiv ℝ (u₁ i) 0) (u₂ i) lam
          eLpNorm (fun y => χ y * (v₂ y - v₁ y) / (r y) ^ 2) 2
            (volume.restrict Y) ≤ ENNReal.ofReal D := by
  sorry

end CalderonPaper
