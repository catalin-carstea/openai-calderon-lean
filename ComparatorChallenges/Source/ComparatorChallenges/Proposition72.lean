module

public import Proof.CalderonPatch.MeasuredCommonCap

public section

open Set
open scoped ContDiff Manifold
open CalderonPatch

namespace CalderonPaper

/-- Proposition 7.2 of the September 24, 2026 manuscript. The completed
isometry is the same map on the extended interiors, and it carries the
second original copy to the first via a map fixing the measured patch. -/
theorem proposition72 {m : ℕ} (hn : 3 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]

    -- Original Dirichlet data and their identified cap.
    {d₁ d₂ : DirichletData m M}
    {Γ : Set ((𝓡∂ (m + 1)).boundary M)} (hΓ : IsOpen Γ)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (C : MeasuredCommonCap d₁ d₂ Γ)

    -- Isometry of the extended interiors.
    (e : OpenPartialHomeomorph M M)
    (hSource : e.source = (𝓡∂ (m + 1)).interior M)
    (hTarget : e.target = (𝓡∂ (m + 1)).interior M)
    (hIsometry : IsLocalMetricIsometry C.firstMetric C.secondMetric e)
    (hCap : EqOn e C.capMap C.capMap.source) :
    ∃ Φ : M ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ M,
      EqOn Φ e e.source ∧ PullbackMetric C.firstMetric C.secondMetric Φ ∧

      -- Restriction to the original copies and the measured-patch condition.
      ∃ Ψ : M ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ M,
        C.firstCopy.embed ∘ Ψ = Φ ∘ C.secondCopy.embed ∧
        PullbackMetric d₁.metric d₂.metric Ψ ∧ FixesPatch Γ Ψ := sorry

end CalderonPaper
