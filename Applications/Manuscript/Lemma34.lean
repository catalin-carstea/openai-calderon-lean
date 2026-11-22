module

public import Proof.Manuscript.Lemma34

public section

open Set Filter CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

/-- The reference operators propagate the given seed through the entire
cylinder, including the bottom level. -/
theorem lemma34_bottomLevel
    {n : ℕ} [NeZero n] {Z : Type*} [TopologicalSpace Z]
    (e : OpenPartialHomeomorph ((X n) × (X n)) (Z × ℝ))
    {B : Set Z} (hB : IsCompact B) {lo amin amax hi : ℝ}
    (hlo : lo < amin) (hab : amin ≤ amax) (hhi : amax < hi)
    (hchart : B ×ˢ Ioo lo hi ⊆ e.target)
    {D₁ D₂ : Set (X n)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hchartD : e.symm '' (B ×ˢ Ioo lo hi) ⊆ D₁ ×ˢ D₂)
    {S : Set ((X n) × (X n))} (hS : IsOpen S) (hSD : S ⊆ D₁ ×ˢ D₂)
    (htop : e.symm '' (B ×ˢ Ico amax hi) ⊆ S)
    (hside : e.symm '' ((B \ interior B) ×ˢ Icc amin amax) ⊆ S)
    (hup : ∀ z ∈ B, ∀ s t : ℝ, s ∈ Ioo lo hi → t ∈ Ioo lo hi →
      s ≤ t → e.symm (z, s) ∈ S → e.symm (z, t) ∈ S)
    (L₁ L₂ : ℝ → ScalarElliptic n)
    (hL₁ : ScalarElliptic.SmoothFamilyOn L₁ D₁)
    (hL₂ : ScalarElliptic.SmoothFamilyOn L₂ D₂)
    (ρ : ℝ → ((X n) × (X n)) → ℝ)
    (hsmooth : ∀ a ∈ Icc amin amax, ContDiffOn ℝ ∞ (ρ a) (e.symm '' (interior B ×ˢ Ioo lo hi)))
    (hzero : ∀ a ∈ Icc amin amax, ∀ z ∈ interior B, ρ a (e.symm (z, a)) = 0)
    (hsign : ∀ a ∈ Icc amin amax, ∀ z ∈ interior B, ∀ t ∈ Ioo lo hi,
      0 < ρ a (e.symm (z, t)) ↔ a < t)
    (hstrict : ∀ a ∈ Icc amin amax, ∀ z ∈ interior B, e.symm (z, a) ∉ S →
      ProductStrictHessianAt (L₁ 0).metric (L₂ 0).metric (ρ a) (e.symm (z, a)))
    (F : (X n) × (X n) → ℝ) (hF : (L₁ 0).ProductSolvesOn (L₂ 0) S F) :
    ∃ (O : Set ((X n) × (X n))) (G : (X n) × (X n) → ℝ),
      IsOpen O ∧ S ⊆ O ∧ e.symm '' (B ×ˢ ({amin} : Set ℝ)) ⊆ O ∧
      (L₁ 0).ProductSolvesOn (L₂ 0) O G ∧ EqOn G F S := by
  obtain ⟨O, hO, hcover, _, hcontinue, _⟩ := lemma34 e hB hlo hab hhi hchart hD₁ hD₂ hchartD
    hS hSD htop hside hup (L₁ 0) (L₂ 0) (hL₁.1 0) (hL₂.1 0) ρ hsmooth hzero hsign hstrict
  obtain ⟨G, hG, heq⟩ := (hcontinue L₁ L₂ ⟨hL₁, hL₂, rfl, rfl⟩).self_of_nhds F hF
  have hsingleton : ({amin} : Set ℝ) ⊆ Icc amin amax := singleton_subset_iff.mpr ⟨le_rfl, hab⟩
  exact ⟨O, G, hO, subset_union_left.trans hcover,
    (image_mono (prod_mono Subset.rfl hsingleton)).trans
      (subset_union_right.trans hcover), hG, heq⟩

end CalderonPaper
