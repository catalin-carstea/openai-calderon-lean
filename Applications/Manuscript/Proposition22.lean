module

public import Proof.Manuscript.Proposition22

public section

open MeasureTheory Set
open scoped ContDiff Manifold
open CalderonN (IsDirichletGreenKernel)
open CalderonPatch

namespace CalderonPaper

local notation "J[" m "]" => 𝓡∂ (m+1)
local notation "Source[" m "," M "]" => smoothSourceSubmodule (m := m) (M := M)
local notation "inverse[" D "]" => DirichletData.smoothInverse D (nativeInverseRegularity D)

theorem matchedCapKernels {m : ℕ} (hn : 3 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (J[m]) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (d₁ d₂ : DirichletData m M)
    {Γ : Set ((J[m]).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ) :

    ∃ C : MeasuredCommonCap d₁ d₂ Γ, ∃ (μ₁ μ₂ : Measure M) (G₁ G₂ : M × M → ℝ),
      IsDirichletGreenKernel (J[m]) μ₁ (nativeLaplace C.firstMetric) G₁ ∧
      IsDirichletGreenKernel (J[m]) μ₂ (nativeLaplace C.secondMetric) G₂ ∧
      ∀ p ∈ C.capMap.source, ∀ q ∈ C.capMap.source, p ≠ q →
        G₁ (C.capMap p, C.capMap q) = G₂ (p, q) := by
  obtain ⟨C, _, _, _, _, _, _, μ₁, μ₂, _, _, G₁, G₂, hG₁, hG₂, _, _, hEqual, _⟩ :=
    proposition22 hn d₁ d₂ hΓ hΓne hEnergy
  exact ⟨C, μ₁, μ₂, G₁, G₂, hG₁, hG₂, hEqual⟩

end CalderonPaper
