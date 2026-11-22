module

public import Proof.CalderonN.ConformalDepth
public import Proof.CalderonN.RadiusProfileGeometry
public import Proof.CalderonN.CylinderCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

open Set Filter
open scoped BigOperators Topology
open CalderonN

namespace CalderonPaper

/-- Lemma 4.1 for the conformal depth and logarithmic softplus radius of §4.
The fixed choice of conformal depth is made before all radius parameters. -/
theorem lemma41
    {n : ℕ} [NeZero n] (normal : I n)
    {Ω : Set (X n)} (hΩ : IsOpen Ω) (h0 : (0 : X n) ∈ Ω)
    {g : MetricField n} (hg : SmoothMetric Ω g) (hg0 : g 0 = 1) :
    ∃ L > 0, ∃ c > 0, ∃ C : ℕ → ℝ,
      let Y := coordinateCylinder normal
      let t := conformalDepth normal L
      let γ := conformalReference (depthScale normal L) g
      let r := fun R p => shrinkingRadius R p t
      (∃ lam₀ > 0,
        (∀ lam ∈ Ioo (0 : ℝ) lam₀, ∀ p : ℕ, 2 ≤ p → ∀ R > 0, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y,
          let f := fun z => Real.log (r R p δ z)
          let b := beta (γ lam) (r R p δ) y
          c * (p : ℝ) ≤ b ∧
          (∀ v : X n,
            (∑ i, ∑ j, metricHessian (γ lam) f y i j * v i * v j)
              ≤ -c * b * metricPair (γ lam) y v v) ∧
          (∀ j : ℕ, 1 ≤ j → ‖iteratedFDeriv ℝ j f y‖ ≤ C j * b ^ j)) ∧
        (∀ p : ℕ, 2 ≤ p → ∀ ε > 0, ∃ R₀ > 0,
          ∀ R ∈ Ioo (0 : ℝ) R₀, ∀ lam ∈ Ioo (0 : ℝ) lam₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y,
            r R p δ y * (beta (γ lam) (r R p δ) y) ^ 2 ≤ ε)) ∧
      ∀ p : ℕ, 2 ≤ p → ∀ R > 0,
        (∃ l, ∀ δ ∈ Ioc (0 : ℝ) 1,
          LipschitzOnWith l (fun y => (r R p δ y) ^ (1 / (p : ℝ))) Y) ∧
        (∀ y ∈ Y, StrictMonoOn (fun δ => r R p δ y) (Ioc (0 : ℝ) 1)) ∧
        ∀ y ∈ Y, t y ≤ 0 → Tendsto (fun δ => r R p δ y) (𝓝[>] 0) (𝓝 0) := by
  sorry

end CalderonPaper
