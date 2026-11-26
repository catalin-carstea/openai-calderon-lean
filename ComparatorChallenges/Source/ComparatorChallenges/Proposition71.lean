module

public import Proof.CalderonPatch.NativeCapSourceFamily
public import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Proof.CalderonPatch.NativeInverseRegularityProof

public section

open Set
open scoped ContDiff Manifold
open CalderonPatch

namespace CalderonPaper

local notation "J[" m "]" => 𝓡∂ (m+1)
local notation "Source[" k "," N "]" => smoothSourceSubmodule (m := k) (M := N)
local notation "inverse[" D "]" => DirichletData.smoothInverse D (nativeInverseRegularity D)

/-- Proposition 7.1 of the September 24, 2026 manuscript. The identified
cap and the common supported source evaluations are extended by one
surjective isometry of the interiors. -/
theorem proposition71 {m : ℕ} (hn : 3 ≤ m + 1) {N₁ N₂ : Type*}
    [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁] [ConnectedSpace N₁]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) N₁] [IsManifold (J[m]) ∞ N₁]
    [MeasurableSpace N₁] [BorelSpace N₁]
    [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂] [ConnectedSpace N₂]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) N₂] [IsManifold (J[m]) ∞ N₂]
    [MeasurableSpace N₂] [BorelSpace N₂]

    -- Dirichlet data and the cap map from the second manifold to the first.
    (D₁ : DirichletData m N₁) (D₂ : DirichletData m N₂)
    (cap : OpenPartialHomeomorph N₂ N₁)
    (hCapIso : IsLocalMetricIsometry D₁.metric D₂.metric cap)
    (hCap₁ : cap.target ⊆ (J[m]).interior N₁) (hCap₂ : cap.source ⊆ (J[m]).interior N₂)
    (hCapConn : IsConnected cap.source)

    -- Common source region and agreement of the inverse evaluations.
    (U₀ : Set N₂) (hOpen : IsOpen U₀) (hNonempty : U₀.Nonempty)
    (hCompact : IsCompact (closure U₀)) (hInside : closure U₀ ⊆ cap.source)
    (hAgreement : ∀ (f₁ : Source[m, N₁]) (f₂ : Source[m, N₂]),
      tsupport (f₁ : N₁ → ℝ) ⊆ cap '' U₀ → tsupport (f₂ : N₂ → ℝ) ⊆ U₀ →
      EqOn ((f₁ : N₁ → ℝ) ∘ cap) f₂ U₀ →
      EqOn (inverse[D₁] f₁ ∘ cap) (inverse[D₂] f₂) cap.source) :

    -- Extension to both interiors with the same evaluation agreement.
    ∃ Φ : OpenPartialHomeomorph N₂ N₁,
      Φ.source = (J[m]).interior N₂ ∧ Φ.target = (J[m]).interior N₁ ∧
      IsLocalMetricIsometry D₁.metric D₂.metric Φ ∧ EqOn Φ cap cap.source ∧
      ∀ (f₁ : Source[m, N₁]) (f₂ : Source[m, N₂]),
        tsupport (f₁ : N₁ → ℝ) ⊆ cap '' U₀ → tsupport (f₂ : N₂ → ℝ) ⊆ U₀ →
        EqOn ((f₁ : N₁ → ℝ) ∘ cap) f₂ U₀ →
        EqOn (inverse[D₁] f₁ ∘ Φ) (inverse[D₂] f₂) Φ.source := sorry

end CalderonPaper
