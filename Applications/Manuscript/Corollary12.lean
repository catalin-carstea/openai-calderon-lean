module

public import Proof.Manuscript.Corollary12

public section

open Set MeasureTheory CalderonPatch
open scoped ContDiff Manifold

namespace CalderonPaper

theorem fullBoundaryFixesSpecifiedPoint {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (p : ↥((𝓡∂ n).boundary M))
    {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ univ) :
    ∃ F : M ≃ₘ⟮𝓡∂ n, 𝓡∂ n⟯ M, F p = (p : M) ∧ PullbackMetric g₂ g₁ F := by
  obtain ⟨F, hFix, hPull⟩ := corollary12 (M := M) hn ⟨(p : M), p.property⟩ hμ₁ hμ₂ hEnergy
  exact ⟨F, hFix p (mem_univ p), hPull⟩

end CalderonPaper
