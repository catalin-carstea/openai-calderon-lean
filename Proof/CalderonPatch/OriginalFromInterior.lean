module

public import Proof.CalderonPatch.SmoothInteriorIsometry
public import Proof.CalderonPatch.ReturnToOriginal

public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M N₁ N₂ : Type*}
  [TopologicalSpace M] [CompactSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M]
  [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁] [ChartedSpace (EuclideanHalfSpace n) N₁]
  [IsManifold (𝓡∂ n) ∞ N₁]
  [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂] [ChartedSpace (EuclideanHalfSpace n) N₂]
  [IsManifold (𝓡∂ n) ∞ N₂]

local notation "J" => 𝓡∂ n

/-- Complete the global interior match and carry it back to the
original manifolds. Agreement at the addressed seam follows from the
same interior map. -/
theorem original_isometry_of_globalInterior_match {g₁ g₂ : SmoothMetric n M}
    {G₁ : SmoothMetric n N₁} {G₂ : SmoothMetric n N₂} {cap₁ : Set N₁} {cap₂ : Set N₂}
    (O₁ : OriginalCopy g₁ G₁ cap₁) (O₂ : OriginalCopy g₂ G₂ cap₂)
    {e : OpenPartialHomeomorph N₂ N₁} (he : IsLocalMetricIsometry G₁ G₂ e)
    (hs : e.source = (J).interior N₂) (ht : e.target = (J).interior N₁)
    (hCapS : cap₂ ⊆ e.source) (hCap : e '' cap₂ = cap₁)
    {P : Set ((J).boundary M)} (hP : ∀ p ∈ P, O₂.embed p ∈ e.source ∧ e (O₂.embed p) = O₁.embed p) :
    ∃ Ψ : M ≃ₘ⟮J, J⟯ M, FixesPatch P Ψ ∧ PullbackMetric g₁ g₂ Ψ := by
  obtain ⟨Φ,hΦ,hMet⟩ := smoothCompletion_of_interiorIsometry he hs ht
  have hΦCap : Φ '' cap₂ = cap₁ := (Set.image_congr (hΦ.mono hCapS)).trans hCap
  obtain ⟨Ψ,hFix,hPull,_⟩ := restrict_completed_isometry_to_original O₁ O₂ Φ hΦCap hMet
    (fun p hp => (hΦ (hP p hp).1).trans (hP p hp).2)
  exact ⟨Ψ,hFix,hPull⟩

/-- A global interior continuation of the paired cap charts preserves
the cap as a set. Together with seam agreement this recovers the
isometry of the original copies. -/
theorem original_isometry_of_globalInterior_extending_cap {g₁ g₂ : SmoothMetric n M}
    {G₁ : SmoothMetric n N₁} {G₂ : SmoothMetric n N₂}
    (cap : OpenPartialHomeomorph N₂ N₁)
    (O₁ : OriginalCopy g₁ G₁ cap.target) (O₂ : OriginalCopy g₂ G₂ cap.source)
    {e : OpenPartialHomeomorph N₂ N₁} (he : IsLocalMetricIsometry G₁ G₂ e)
    (hs : e.source = (J).interior N₂) (ht : e.target = (J).interior N₁)
    (hCap : cap.source ⊆ (J).interior N₂) (hExtend : EqOn e cap cap.source)
    {P : Set ((J).boundary M)} (hP : ∀ p ∈ P, O₂.embed p ∈ e.source ∧ e (O₂.embed p) = O₁.embed p) :
    ∃ Ψ : M ≃ₘ⟮J, J⟯ M, FixesPatch P Ψ ∧ PullbackMetric g₁ g₂ Ψ := by
  have hImage : e '' cap.source = cap.target :=
    (Set.image_congr hExtend).trans cap.image_source_eq_target
  exact original_isometry_of_globalInterior_match O₁ O₂ he hs ht (hs.symm ▸ hCap) hImage hP

end CalderonPatch
