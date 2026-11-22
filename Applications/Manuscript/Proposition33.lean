module

public import Proof.Manuscript.Proposition33

public section

open Set Filter CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

/-- Apply the strict product test at the reference point of the family. -/
theorem proposition33_continueAtReference
    {n : ℕ} [NeZero n] {D₁ D₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (L₁ L₂ : ℝ → ScalarElliptic n)
    (hL₁ : ScalarElliptic.SmoothFamilyOn L₁ D₁)
    (hL₂ : ScalarElliptic.SmoothFamilyOn L₂ D₂)
    {U : Set ((X n) × (X n))} (hU : IsOpen U) (hUD : U ⊆ D₁ ×ˢ D₂)
    (z₀ : (X n) × (X n)) (hz₀ : z₀ ∈ U)
    (ρ : ℝ → ((X n) × (X n)) → ℝ)
    (hρ : ContDiffOn ℝ ∞ (fun q : ℝ × ((X n) × (X n)) => ρ q.1 q.2) (univ ×ˢ U))
    (hρref : ContDiffOn ℝ ∞ (ρ 0) U)
    (hρ₀ : ρ 0 z₀ = 0)
    (hstrict : ProductStrictHessianAt (L₁ 0).metric (L₂ 0).metric (ρ 0) z₀)
    (F : (X n) × (X n) → ℝ)
    (hF : (L₁ 0).ProductSolvesOn (L₂ 0) {z ∈ U | 0 < ρ 0 z} F) :
    ∃ (V : Set ((X n) × (X n))) (G : (X n) × (X n) → ℝ),
      IsOpen V ∧ z₀ ∈ V ∧ (L₁ 0).ProductSolvesOn (L₂ 0) V G ∧
      EqOn G F (V ∩ {z ∈ U | 0 < ρ 0 z}) := by
  obtain ⟨V, K₁, K₂, K₃, K₄, ε, hV, hzV, _, _, _, _, _, _, _, hcontinue, _⟩ :=
    proposition33 hD₁ hD₂ (L₁ 0) (L₂ 0) (hL₁.1 0) (hL₂.1 0) hU hUD z₀ hz₀
      (ρ 0) hρref hρ₀ hstrict
  obtain ⟨G, hG, heq⟩ := (hcontinue L₁ L₂ ρ ⟨hL₁, hL₂, hρ, rfl, rfl, rfl⟩).self_of_nhds F hF
  exact ⟨V, G, hV, hzV, hG, heq⟩

end CalderonPaper
