module

public import Proof.CalderonPatch.MeasuredCommonCap
public import Proof.CalderonPatch.SmoothInteriorIsometry

import Proof.CalderonPatch.MeasuredAccessibleGauge
import Mathlib.Tactic

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
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {d₁ d₂ : DirichletData m M}
    {Γ : Set ((𝓡∂ (m+1)).boundary M)} (hΓ : IsOpen Γ)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (C : MeasuredCommonCap d₁ d₂ Γ)
    (e : OpenPartialHomeomorph M M)
    (hSource : e.source = (𝓡∂ (m+1)).interior M)
    (hTarget : e.target = (𝓡∂ (m+1)).interior M)
    (hIsometry : IsLocalMetricIsometry C.firstMetric C.secondMetric e)
    (hCap : EqOn e C.capMap C.capMap.source) :
    ∃ Φ : M ≃ₘ⟮𝓡∂ (m+1), 𝓡∂ (m+1)⟯ M,
      EqOn Φ e e.source ∧ PullbackMetric C.firstMetric C.secondMetric Φ ∧
      ∃ Ψ : M ≃ₘ⟮𝓡∂ (m+1), 𝓡∂ (m+1)⟯ M,
        C.firstCopy.embed ∘ Ψ = Φ ∘ C.secondCopy.embed ∧
        PullbackMetric d₁.metric d₂.metric Ψ ∧ FixesPatch Γ Ψ := by
  have hm : 2 ≤ m := by omega
  obtain ⟨Φ, hExtend, hMetric⟩ :=
    smoothCompletion_of_interiorIsometry hIsometry hSource hTarget
  have hCapInterior : C.capMap.source ⊆ e.source := hSource.symm ▸ C.source_interior
  have hCapImage : Φ '' C.capMap.source = C.capMap.target :=
    (Set.image_congr ((hExtend.mono hCapInterior).trans hCap)).trans
      C.capMap.image_source_eq_target
  have hSeam : ∀ p ∈ C.patch, Φ (C.secondCopy.embed p) = C.firstCopy.embed p := by
    intro p hp
    obtain ⟨hpSource, hpEq⟩ := C.seam e hSource hCap p hp
    exact (hExtend hpSource).trans hpEq
  obtain ⟨Ψ, hFix, hPull, hCommute⟩ := restrict_completed_isometry_to_original
    C.firstCopy C.secondCopy Φ hCapImage hMetric hSeam
  have hFixAll := fixesPatch_of_patchEnergy_of_fixes_open_subpatch hm d₁ d₂ hΓ
    C.open_patch C.nonempty_patch C.patch_subset hEnergy Ψ hPull hFix
  exact ⟨Φ, hExtend, hMetric, Ψ, hCommute, hPull, hFixAll⟩


end CalderonPaper
