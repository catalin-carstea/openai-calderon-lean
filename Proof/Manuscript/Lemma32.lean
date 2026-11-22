module

public import Proof.Manuscript.ScalarElliptic

import Proof.Manuscript.ScalarUniformCross
import Mathlib.Tactic

public section

open Set MeasureTheory
open CalderonN CalderonPaper.ScalarElliptic

namespace CalderonPaper

set_option linter.unusedVariables false in
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
  have hSc₁ : IsCompact (closure S₁) :=
    hDb₁.of_isClosed_subset isClosed_closure (hS₁D.trans subset_closure)
  have hD₂finite : (volume : Measure (X n)) D₂ ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hDb₂.measure_lt_top).ne
  have hSD₂ : S₂ ⊆ D₂ := subset_closure.trans hS₂D
  have hOD₁ : O₁ ⊆ D₁ := subset_closure.trans hO₁D
  have hOD₂ : O₂ ⊆ D₂ := subset_closure.trans hO₂D
  constructor
  · intro L₁ L₂ hL₁ hL₂ hi₁ hi₂
    exact exists_scalar_crossExtension_fixed hD₁ hD₂ hconn₁ hconn₂ hD₂finite
      hS₁ hS₂ hnon₁ hnon₂ hO₁ hO₂ hSc₁ hS₁D hSD₂ hOD₁ hOD₂ hL₁ hL₂
      hC₁.le hC₂.le hγ₂.1 hγ₂.2.le (sub_pos.mpr hmargin) hi₁ hi₂
  · intro ε hε K hK hKc m
    obtain ⟨N,hN⟩ := exists_numeric_scalar_crossExtension hD₁ hD₂ hconn₁ hconn₂ hD₂finite
      hS₁ hS₂ hnon₁ hnon₂ hO₁ hO₂ hSc₁ hS₁D hSD₂ hOD₁ hOD₂ hC₁.le hC₂.le ε hε hK hKc m
    refine ⟨N,fun a A ha hA => ?_⟩
    obtain ⟨C,hC,hBound⟩ := hN a A ha hA
    exact ⟨C,hC,fun δ₁ δ₂ _ h₂ hm => hBound δ₁ δ₂ h₂.1 h₂.2.le hm⟩

end CalderonPaper
