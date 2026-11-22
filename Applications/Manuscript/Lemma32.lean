module

public import Proof.Manuscript.Lemma32

public section

open Set
open CalderonN CalderonPaper.ScalarElliptic

namespace CalderonPaper

/-- On either intersection the continued function takes the prescribed
values of the original cross, with no containment of observed sets in output
sets assumed. -/
theorem lemma32_prescribedOverlap
    {n : ℕ} [NeZero n]
    {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hconn₁ : IsConnected D₁) (hconn₂ : IsConnected D₂)
    (hDb₁ : IsCompact (closure D₁)) (hDb₂ : IsCompact (closure D₂))
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hnon₁ : S₁.Nonempty) (hnon₂ : S₂.Nonempty)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hS₁D : closure S₁ ⊆ D₁) (hS₂D : closure S₂ ⊆ D₂)
    (hO₁D : closure O₁ ⊆ D₁) (hO₂D : closure O₂ ⊆ D₂)
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hγ₁ : γ₁ ∈ Ioo (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Ioo (0 : ℝ) 1) (hmargin : 1 < γ₁ + γ₂)
    {L₁ L₂ : ScalarElliptic n} (hL₁ : L₁.SmoothOn D₁) (hL₂ : L₂.SmoothOn D₂)
    (hi₁ : L₁.Interpolates D₁ S₁ O₁ C₁ γ₁) (hi₂ : L₂.Interpolates D₂ S₂ O₂ C₂ γ₂)
    {F : (X n) × (X n) → ℝ} {M : ℝ} (hF : CrossData L₁ L₂ D₁ D₂ S₁ S₂ F M) :
    ∃ G, L₁.ProductSolvesOn L₂ (O₁ ×ˢ O₂) G ∧
      EqOn G F ((O₁ ×ˢ (O₂ ∩ S₂)) ∪ ((O₁ ∩ S₁) ×ˢ O₂)) := by
  obtain ⟨C, hC⟩ := (lemma32 hD₁ hD₂ hconn₁ hconn₂ hDb₁ hDb₂ hS₁ hS₂ hnon₁ hnon₂
    hO₁ hO₂ hS₁D hS₂D hO₁D hO₂D hC₁ hC₂ hγ₁ hγ₂ hmargin).1 L₁ L₂ hL₁ hL₂ hi₁ hi₂
  obtain ⟨G, ⟨hG, hleft, hright⟩, _⟩ := hC F M hF
  exact ⟨G, hG, hleft.union hright⟩

end CalderonPaper
