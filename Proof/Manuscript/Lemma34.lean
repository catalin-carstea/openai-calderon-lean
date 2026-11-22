module

public import Proof.Manuscript.ScalarElliptic

import Proof.Manuscript.ScalarCylinderLocal
import Proof.Manuscript.ScalarProductCompactJets
import Mathlib.Tactic

public section

open Set Filter CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

/-- Lemma 3.4. Sweep the compact cylinder from its seeded top and lateral
boundary. The fixed compact data used for a quantitative extension are
contained in the initially given region. -/
theorem lemma34
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
    (L₁₀ L₂₀ : ScalarElliptic n)
    (hL₁₀ : L₁₀.SmoothOn D₁) (hL₂₀ : L₂₀.SmoothOn D₂)
    (ρ : ℝ → ((X n) × (X n)) → ℝ)
    (hsmooth : ∀ a ∈ Icc amin amax, ContDiffOn ℝ ∞ (ρ a) (e.symm '' (interior B ×ˢ Ioo lo hi)))
    (hzero : ∀ a ∈ Icc amin amax, ∀ z ∈ interior B, ρ a (e.symm (z, a)) = 0)
    (hsign : ∀ a ∈ Icc amin amax, ∀ z ∈ interior B, ∀ t ∈ Ioo lo hi,
      0 < ρ a (e.symm (z, t)) ↔ a < t)
    (hstrict : ∀ a ∈ Icc amin amax, ∀ z ∈ interior B, e.symm (z, a) ∉ S →
      ProductStrictHessianAt L₁₀.metric L₂₀.metric (ρ a) (e.symm (z, a))) :
    ∃ O : Set ((X n) × (X n)), IsOpen O ∧ S ∪ e.symm '' (B ×ˢ Icc amin amax) ⊆ O ∧
      O ⊆ D₁ ×ˢ D₂ ∧
      let admissible := fun (L₁ L₂ : ℝ → ScalarElliptic n) =>
        ScalarElliptic.SmoothFamilyOn L₁ D₁ ∧ ScalarElliptic.SmoothFamilyOn L₂ D₂ ∧
        L₁ 0 = L₁₀ ∧ L₂ 0 = L₂₀
      (∀ L₁ L₂, admissible L₁ L₂ → ∀ᶠ s in 𝓝 (0 : ℝ), ∀ F,
        (L₁ s).ProductSolvesOn (L₂ s) S F →
        ∃ G, (L₁ s).ProductSolvesOn (L₂ s) O G ∧ EqOn G F S) ∧
      ∀ K ⊆ O, IsCompact K → ∀ m : ℕ, ∃ (K₀ : Set ((X n) × (X n))) (C : ℝ),
        IsCompact K₀ ∧ K₀ ⊆ S ∧ 0 ≤ C ∧
        ∀ L₁ L₂, admissible L₁ L₂ →
        ∀ᶠ s in 𝓝 (0 : ℝ), ∀ F, (L₁ s).ProductSolvesOn (L₂ s) S F →
        ∀ M : ℝ, 0 ≤ M → (∀ q ∈ K₀, |F q| ≤ M) →
        ∃ G, (L₁ s).ProductSolvesOn (L₂ s) O G ∧ EqOn G F S ∧
          ∀ k ≤ m, ∀ q ∈ K, ‖iteratedFDeriv ℝ k G q‖ ≤ C * M := by
  obtain ⟨O,hO,hCover,hOD,hQual,hQuant⟩ := scalar_cylinder_sweep_of_local_extensions
    e hB hlo hab hhi hchart hchartD hS hSD htop hside L₁₀ L₂₀
    (fun a ha z hz hzS => exists_reference_scalar_cylinder_local e (hlo.trans_le ha.1)
      (ha.2.trans_lt hhi) hchart hD₁ hD₂ hchartD hS hup hL₁₀ hL₂₀
      (hsmooth a ha) (hsign a ha) z hz (hzero a ha z hz) (hstrict a ha z hz hzS))
    (fun V hV hVD K hKV hK m => exists_reference_scalar_product_compact_jet_bound hV hVD hD₁ hD₂
      hL₁₀ hL₂₀ hKV hK m)
  refine ⟨O,hO,hCover,hOD,?_,?_⟩
  · intro L₁ L₂ hAdm
    exact hQual ⟨L₁,L₂,hAdm.1,hAdm.2.1,hAdm.2.2.1,hAdm.2.2.2⟩
  · intro K hKO hK m
    obtain ⟨L,C,hL,hLS,hC,hBd⟩ := hQuant K hKO hK m
    exact ⟨L,C,hL,hLS,hC,fun L₁ L₂ hAdm =>
      hBd ⟨L₁,L₂,hAdm.1,hAdm.2.1,hAdm.2.2.1,hAdm.2.2.2⟩⟩

end CalderonPaper
