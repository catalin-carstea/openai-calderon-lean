module

public import Proof.CalderonPatch.Energy

public section

open Set MeasureTheory
open scoped ContDiff Manifold

namespace CalderonPatch

/-- Theorem 1.1, in the equivalent smooth quadratic Dirichlet energy formulation. -/
theorem smoothAnisotropicUniqueness {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {Γ : Set ((𝓡∂ n).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty) (hΓproper : Γ ≠ univ)
    {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ) :
    ∃ Φ : M ≃ₘ⟮𝓡∂ n, 𝓡∂ n⟯ M, FixesPatch Γ Φ ∧ PullbackMetric g₁ g₂ Φ := by
  sorry

end CalderonPatch
