module

public import Proof.CalderonPatch.Energy

public section

open Set MeasureTheory CalderonPatch
open scoped ContDiff Manifold

namespace CalderonPaper

/-- Corollary 1.2. Full-boundary uniqueness. -/
theorem corollary12 {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]

    -- Full boundary, with its metric volume and energy data.
    (hBoundary : ((𝓡∂ n).boundary M).Nonempty)
    {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ univ) :
    ∃ F : M ≃ₘ⟮𝓡∂ n, 𝓡∂ n⟯ M, FixesPatch (n := n) univ F ∧ PullbackMetric g₂ g₁ F := by sorry

end CalderonPaper
