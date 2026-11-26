module

public import Proof.CalderonPatch.NativeCapAgreement

public section

open MeasureTheory Set
open scoped ContDiff Manifold
open CalderonN (IsDirichletGreenKernel)
open CalderonPatch

namespace CalderonPaper

local notation "J[" m "]" => 𝓡∂ (m+1)
local notation "Source[" m "," M "]" => smoothSourceSubmodule (m := m) (M := M)
local notation "inverse[" D "]" => DirichletData.smoothInverse D (nativeInverseRegularity D)

/-- Proposition 2.2 of the September 24, 2026 manuscript. Both metrics
extend over the identified cap. The original boundary portion that
moves into the interior is compactly contained in the measured patch.
The actual kernels and canonical inverse solutions agree on the cap. -/
theorem proposition22 {m : ℕ} (hn : 3 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (J[m]) ∞ M]
    [MeasurableSpace M] [BorelSpace M]

    -- Measured Dirichlet data.
    (d₁ d₂ : DirichletData m M)
    {Γ : Set ((J[m]).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ) :
    ∃ C : MeasuredCommonCap d₁ d₂ Γ,

      -- The part of the old boundary that becomes interior.
      ∃ P₀ : Set ((J[m]).boundary M),
        IsOpen P₀ ∧ P₀.Nonempty ∧ IsCompact (closure P₀) ∧ closure P₀ ⊆ Γ ∧
        (P₀ : Set ((J[m]).boundary M)) =
          {p : (J[m]).boundary M | C.secondCopy.embed (p : M) ∈ (J[m]).interior M} ∧

        -- Metric volumes, Green kernels, and agreement off the diagonal.
        ∃ (μ₁ μ₂ : Measure M) (hμ₁ : IsMetricVolume C.firstMetric μ₁)
            (hμ₂ : IsMetricVolume C.secondMetric μ₂) (G₁ G₂ : M × M → ℝ),
          IsDirichletGreenKernel (J[m]) μ₁ (nativeLaplace C.firstMetric) G₁ ∧
          IsDirichletGreenKernel (J[m]) μ₂ (nativeLaplace C.secondMetric) G₂ ∧
          RepresentsNativeInverse (nativeInverseRegularity (C.firstData μ₁ hμ₁)) G₁ ∧
          RepresentsNativeInverse (nativeInverseRegularity (C.secondData μ₂ hμ₂)) G₂ ∧
          (∀ p ∈ C.capMap.source, ∀ q ∈ C.capMap.source, p ≠ q →
            G₁ (C.capMap p, C.capMap q) = G₂ (p, q)) ∧

          -- Agreement of the canonical inverses for matched sources.
          ∀ (f₁ f₂ : Source[m, M]),
            tsupport (f₁ : M → ℝ) ⊆ C.capMap.target →
            tsupport (f₂ : M → ℝ) ⊆ C.capMap.source →
            EqOn ((f₁ : M → ℝ) ∘ C.capMap) f₂ C.capMap.source →
            EqOn (inverse[C.firstData μ₁ hμ₁] f₁ ∘ C.capMap)
              (inverse[C.secondData μ₂ hμ₂] f₂) C.capMap.source := sorry

end CalderonPaper
