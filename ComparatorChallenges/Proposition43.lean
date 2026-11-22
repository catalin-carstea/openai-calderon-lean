module

public import ComparatorChallenges.Frozen.Manuscript.TransferDensity
public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.GreenCross
public import Proof.CalderonN.GreenDilation
public import Proof.CalderonN.ConformalDepth
public import Proof.CalderonN.CylinderCutoff
public import Proof.CalderonN.NormalInverse
public import Proof.CalderonN.Radius
public import Proof.CalderonN.MovingSphere.RadiusSeed
public import Proof.CalderonN.SmoothMetricFrame

public section

open Set Filter Metric MeasureTheory CalderonN
open CalderonN.FixedTube CalderonN.MovingSphere
open scoped ContDiff Topology

namespace CalderonPaper

/-- Proposition 4.3 for the continued kernel of the shrinking-sphere
construction, using the same kernel in the flux and the seed agreements. -/
theorem proposition43
    {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (hn : 3 ≤ n) (normal : I n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {a : ℕ} {u₁ u₂ : Fin a → X n → ℝ}
    (hu₁ : ∀ i, Harmonic Ω g₁ (u₁ i)) (hu₂ : ∀ i, Harmonic Ω g₂ (u₂ i))
    (hpair : ∀ i, EqOn (u₁ i) (u₂ i) W)
    {p : ℕ} (hp : 2 ≤ p) {ρ R ε tb : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 < ε) (htb : 0 < tb)
    {E : ℝ → (X n) × (X n) → X n}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X n) × (X n)) => E q.1 q.2))
    {lam₀ : ℝ} (hlam₀ : 0 < lam₀)
    (hNormal : ∀ lam ∈ Icc (-lam₀) lam₀,
      NormalCoordinates (closedBall (0 : X n) (5/2)) (ball (0 : X n) 3)
        (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ coordinateCylinder normal,
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ / 2)
    (ht : ∀ y, conformalDepth normal 4 y ≤ 3 * tb → parabolicHeight normal y < 1/4)
    {d : ℝ} (hd : 0 < d)
    (mixedKernel : ℝ → ℝ → (X n) × (X n) → ℝ)
    (continuation :
      let Y := interior (coordinateCylinder normal)
      let Z := closedBall (0 : X n) (5/2)
      let t := conformalDepth normal 4
      let γ := conformalReference (depthScale normal 4) g₁
      let r := shrinkingRadius R p t
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
        let N := normalPairDomain (interior Z) (γ lam) ρ (E lam)
        let q₁ := dilatedMetric g₁ lam
        let q₂ := dilatedMetric g₂ lam
        ball (0 : X n) 3 ⊆ {y | lam • y ∈ Ω} ∧
        ∃ (O₀ : Set ((X n) × (X n))) (F : (X n) × (X n) → ℝ),
          IsOpen O₀ ∧ fixedSeparationSet 4 (d/2) ⊆ O₀ ∧
          ProductSolutionOn q₁ q₂ O₀ F ∧ (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ C₀) ∧
          ∀ δ ∈ Ioc (0 : ℝ) 1, Small Y (γ lam) q₂ (r δ) ε →
            let G := mixedKernel lam δ
            ∃ O : Set ((X n) × (X n)),
              IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
              lowerNormalSeed normal N ⊆ O ∧
              EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) ∧
              (∀ w ∈ bundle Y (γ lam), (endpoint (E lam) (r δ) w, w.1) ∈ O) ∧
              (∀ w ∈ bundle Y (γ lam), tb < t w.1 →
                let q := (endpoint (E lam) (r δ) w, w.1)
                q ∈ fixedSeparationSet 3 d ∧ G =ᶠ[𝓝 q] F) ∧
              ∀ w ∈ bundle Y (γ lam), w.1 normal < -(1/4 : ℝ) →
                let q := (endpoint (E lam) (r δ) w, w.1)
                ‖q.1‖ ≤ 3 ∧ ‖q.2‖ ≤ 3 ∧ G =ᶠ[𝓝 q] dilatedGreen G₁ lam) :
    let Y := interior (coordinateCylinder normal)
    let t := conformalDepth normal 4
    let γ := conformalReference (depthScale normal 4) g₁
    let r := shrinkingRadius R p t
    let χ := cylinderCutoff normal 4 tb
    ∃ C : ℕ → ℝ, ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      let q₁ := dilatedMetric g₁ lam
      let q₂ := dilatedMetric g₂ lam
      let e : Frame n := fun y => smoothMetricFrame (γ lam y)
      ∀ δ ∈ Ioc (0 : ℝ) 1, Small Y (γ lam) q₂ (r δ) ε →
        ∃ (O : Set ((X n) × (X n))) (ψ : (X n) × (X n) → ℝ),
          let G := mixedKernel lam δ
          let T := densityValue (E lam) e (r δ) ψ
          let N := normalPairDomain (interior (closedBall (0 : X n) (5/2))) (γ lam) ρ (E lam)
          IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
          lowerNormalSeed normal N ⊆ O ∧ EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) ∧
          (∀ w ∈ bundle Y (γ lam), (endpoint (E lam) (r δ) w, w.1) ∈ O) ∧
          smoothNear ψ (bundle Y (γ lam)) ∧
          (∀ y ∈ Y, ∀ u, HarmonicOnBall q₁ (closedBallImage (γ lam) (E lam) (r δ) y) u →
            T u y = normalSphereGreenFlux q₁ (E lam) e (r δ) G y u) ∧
          (∀ y₀ ∈ Y, ∀ U : Set (X n), IsOpen U → ∀ u, Harmonic U q₁ u →
            closedBallImage (γ lam) (E lam) (r δ) y₀ ⊆ U →
            ∃ V : Set (X n), IsOpen V ∧ y₀ ∈ V ∧ V ⊆ Y ∧
              (∀ y ∈ V, closedBallImage (γ lam) (E lam) (r δ) y ⊆ U) ∧ Harmonic V q₂ (T u)) ∧
          (∀ y ∈ Y,
            (∫ w : ↥(standardSphere n), ψ (y, frameVector e y w) ∂(sphereProbability n)) = 1 ∧
            (∀ i : I n, T (fun x => x i) y = y i) ∧
            ∀ i : Fin a, T (fun x => u₁ i (lam • x)) y = u₂ i (lam • y)) ∧
          ∀ y ∈ Y, y ∈ tsupport (fderiv ℝ χ) → ∀ w : ↥(standardSphere n), angularBaseJetBound e ψ y w C := by
  sorry

end CalderonPaper
