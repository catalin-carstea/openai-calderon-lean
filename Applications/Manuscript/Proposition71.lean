module

public import Proof.Manuscript.Proposition71

public section

open Set
open scoped ContDiff Manifold
open CalderonPatch

namespace CalderonPaper

local notation "J[" m "]" => 𝓡∂ (m+1)
local notation "Source[" k "," N "]" => smoothSourceSubmodule (m := k) (M := N)
local notation "inverse[" D "]" => DirichletData.smoothInverse D (nativeInverseRegularity D)

theorem capMatchExtendsAllEvaluations {m : ℕ} (hn : 3 ≤ m + 1) {N₁ N₂ : Type*}
    [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁] [ConnectedSpace N₁]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₁] [IsManifold (J[m]) ∞ N₁]
    [MeasurableSpace N₁] [BorelSpace N₁]
    [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂] [ConnectedSpace N₂]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₂] [IsManifold (J[m]) ∞ N₂]
    [MeasurableSpace N₂] [BorelSpace N₂]
    (D₁ : DirichletData m N₁) (D₂ : DirichletData m N₂)
    (cap : OpenPartialHomeomorph N₂ N₁)
    (hCapIso : IsLocalMetricIsometry D₁.metric D₂.metric cap)
    (hCap₁ : cap.target ⊆ (J[m]).interior N₁) (hCap₂ : cap.source ⊆ (J[m]).interior N₂)
    (hCapConn : IsConnected cap.source)
    (U₀ : Set N₂) (hOpen : IsOpen U₀) (hNonempty : U₀.Nonempty)
    (hCompact : IsCompact (closure U₀)) (hInside : closure U₀ ⊆ cap.source)
    (hAgreement : ∀ (f₁ : Source[m, N₁]) (f₂ : Source[m, N₂]),
      tsupport (f₁ : N₁ → ℝ) ⊆ cap '' U₀ → tsupport (f₂ : N₂ → ℝ) ⊆ U₀ →
      EqOn ((f₁ : N₁ → ℝ) ∘ cap) f₂ U₀ →
      EqOn (inverse[D₁] f₁ ∘ cap) (inverse[D₂] f₂) cap.source)
    (f₁ : Source[m, N₁]) (f₂ : Source[m, N₂])
    (hf₁ : tsupport (f₁ : N₁ → ℝ) ⊆ cap '' U₀) (hf₂ : tsupport (f₂ : N₂ → ℝ) ⊆ U₀)
    (hf : EqOn ((f₁ : N₁ → ℝ) ∘ cap) f₂ U₀)
    (p : N₂) (hp : p ∈ (J[m]).interior N₂) :
    ∃ Φ : OpenPartialHomeomorph N₂ N₁,
      Φ.source = (J[m]).interior N₂ ∧ EqOn Φ cap cap.source ∧
      inverse[D₁] f₁ (Φ p) = inverse[D₂] f₂ p := by
  obtain ⟨Φ, hSource, _, _, hMatch, hAll⟩ :=
    proposition71 hn D₁ D₂ cap hCapIso hCap₁ hCap₂ hCapConn U₀ hOpen hNonempty
      hCompact hInside hAgreement
  exact ⟨Φ, hSource, hMatch, hAll f₁ f₂ hf₁ hf₂ hf (hSource.symm ▸ hp)⟩

end CalderonPaper
