module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.Coercivity
public import Proof.CalderonN.GreenRestriction

public section

open Set

namespace CalderonN

/-- Proposition 5.3 for any fixed dimension at least three. -/
theorem coercivity {n : ℕ} (hn : 3 ≤ n) : Coercivity n := by
  sorry

/-- Theorem 3.1 in the common harmonic chart. The ambient Dirichlet
Green kernels are used by their restrictions to the chart. -/
theorem localMetricExtension
    {n : ℕ} (hn : 3 ≤ n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsSmoothSide Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : X n × X n → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {m : ℕ} {u₁ u₂ : Fin m → X n → ℝ}
    (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a)) (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a))
    (hpairs : ∀ a, EqOn (u₁ a) (u₂ a) W) (hspan : HessianSpanning g₁ u₁) :
    ∃ r > 0, Metric.ball (0 : X n) r ⊆ Ω ∧ EqOn g₁ g₂ (Metric.ball 0 r) := by
  sorry

end CalderonN
