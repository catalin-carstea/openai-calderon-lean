module
public import Solution

public section

open Set MeasureTheory
open scoped ContDiff Manifold

namespace CalderonPatch

/-- The same smooth gauge fixes all measured points and preserves the squared length
of every tangent vector, including at the boundary. -/
theorem measuredGaugePreservesTangentEnergy {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {Γ : Set ((𝓡∂ n).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty) (hΓproper : Γ ≠ univ)
    {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ) :
    ∃ Φ : M ≃ₘ⟮𝓡∂ n, 𝓡∂ n⟯ M,
      FixesPatch Γ Φ ∧ ∀ (x : M) (v : TangentSpace (𝓡∂ n) x),
        g₂.inner x v v = g₁.inner (Φ x)
          (mfderiv (𝓡∂ n) (𝓡∂ n) Φ x v) (mfderiv (𝓡∂ n) (𝓡∂ n) Φ x v) := by
  obtain ⟨Φ, hΦΓ, hPullback⟩ :=
    smoothAnisotropicUniqueness hn hΓ hΓne hΓproper hμ₁ hμ₂ hEnergy
  exact ⟨Φ, hΦΓ, fun x v => hPullback x v v⟩

end CalderonPatch
