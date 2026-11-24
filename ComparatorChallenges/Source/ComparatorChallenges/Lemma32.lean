module

public import Proof.Manuscript.ScalarElliptic
public import Proof.CalderonN.Coordinates

public section

open Set
open CalderonN CalderonPaper.ScalarElliptic

namespace CalderonPaper

/-- Lemma 3.2 for general real scalar operators with positive definite
principal matrices, including independent lower-order terms. -/
theorem lemma32
    {n : ℕ} [NeZero n]
    {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hconn₁ : IsConnected D₁) (hconn₂ : IsConnected D₂)
    (hDb₁ : IsCompact (closure D₁)) (hDb₂ : IsCompact (closure D₂))
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hnon₁ : S₁.Nonempty) (hnon₂ : S₂.Nonempty)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hS₁D : closure S₁ ⊆ D₁) (hS₂D : closure S₂ ⊆ D₂)
    (hO₁D : closure O₁ ⊆ D₁) (hO₂D : closure O₂ ⊆ D₂)
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hγ₁ : γ₁ ∈ Ioo (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Ioo (0 : ℝ) 1)
    (hmargin : 1 < γ₁ + γ₂) :
    (∀ L₁ L₂ : ScalarElliptic n,
      L₁.SmoothOn D₁ → L₂.SmoothOn D₂ →
      L₁.Interpolates D₁ S₁ O₁ C₁ γ₁ → L₂.Interpolates D₂ S₂ O₂ C₂ γ₂ →
      ∃ C : Set ((X n) × (X n)) → ℕ → ℝ,
        ∀ F : (X n) × (X n) → ℝ, ∀ M : ℝ, CrossData L₁ L₂ D₁ D₂ S₁ S₂ F M →
        ∃ G, CrossExtension L₁ L₂ S₁ S₂ O₁ O₂ F G ∧
          ∀ K ⊆ O₁ ×ˢ O₂, IsCompact K → ∀ j : ℕ, ∀ z ∈ K,
            ‖iteratedFDeriv ℝ j G z‖ ≤ C K j * M) ∧
    (∀ ε : ℝ, 0 < ε → ∀ K ⊆ O₁ ×ˢ O₂, IsCompact K → ∀ m : ℕ, ∃ N : ℕ,
      ∀ a A : ℝ, 0 < a → 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ₁ δ₂ : ℝ, δ₁ ∈ Ioo (0 : ℝ) 1 → δ₂ ∈ Ioo (0 : ℝ) 1 →
        1 + ε ≤ δ₁ + δ₂ →
      ∀ L₁ L₂ : ScalarElliptic n,
        L₁.SmoothOn D₁ → L₂.SmoothOn D₂ →
        L₁.CoefficientBound D₁ a A N → L₂.CoefficientBound D₂ a A N →
        L₁.Interpolates D₁ S₁ O₁ C₁ δ₁ → L₂.Interpolates D₂ S₂ O₂ C₂ δ₂ →
        ∀ F : (X n) × (X n) → ℝ, ∀ M : ℝ, CrossData L₁ L₂ D₁ D₂ S₁ S₂ F M →
        ∃ G, CrossExtension L₁ L₂ S₁ S₂ O₁ O₂ F G ∧
          ∀ j ≤ m, ∀ z ∈ K, ‖iteratedFDeriv ℝ j G z‖ ≤ C * M) := by
  sorry

end CalderonPaper
