module

public import Proof.CalderonN.WeakEnergyConormalJets

import Mathlib.Tactic

/-! The Poisson difference retains one radius factor in the same
joint jet bounds used by the weak conormal quadratic remainder. -/

public section

noncomputable section
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {P H Z F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[expose] def weakEnergyFirstVariationOperatorL (j : Z →L[ℝ] H)
    (E₀ : H →L[ℝ] H →L[ℝ] ℝ) (P₀ : F →L[ℝ] H) :
    (H →L[ℝ] H →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] H) :=
  -((ContinuousLinearMap.compL ℝ F (Z →L[ℝ] ℝ) H)
      (j.comp (weakEnergyZeroOperatorL j E₀).inverse)).comp
    (((ContinuousLinearMap.compL ℝ F H (Z →L[ℝ] ℝ)).flip P₀).comp (weakEnergyTestOperatorL j))

theorem weakEnergyFirstVariationOperatorL_apply (j : Z →L[ℝ] H)
    (E₀ E₁ : H →L[ℝ] H →L[ℝ] ℝ) (P₀ : F →L[ℝ] H) :
    weakEnergyFirstVariationOperatorL j E₀ P₀ E₁ = weakEnergyFirstVariationL j E₀ E₁ P₀ := by
  ext f : 1
  simp only [weakEnergyFirstVariationOperatorL,weakEnergyFirstVariationL,neg_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]

@[expose] def weakEnergyPoissonDifferenceBudget (j : Z →L[ℝ] H)
    (E₀ : H →L[ℝ] H →L[ℝ] ℝ) (P₀ : F →L[ℝ] H) (N : ℕ) (C I : ℝ) : ℝ :=
  weakEnergyPoissonJetBudget j P₀ N C I+‖weakEnergyFirstVariationOperatorL j E₀ P₀‖*C

theorem localWeakEnergyPoissonDifference_budget
    (j : Z →L[ℝ] H) (E₀ : H →L[ℝ] H →L[ℝ] ℝ)
    (E₁ E₂ : P → H →L[ℝ] H →L[ℝ] ℝ) (P₀ : F →L[ℝ] H)
    (x : P) (r : ℝ) (N : ℕ) (C I : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hI : 0 ≤ I)
    (hE₁ : LocalSmoothJetBudget E₁ x N C) (hE₂ : LocalSmoothJetBudget E₂ x N C)
    (hA₀ : (weakEnergyZeroOperatorL j E₀).IsInvertible)
    (hI₀ : ‖(weakEnergyZeroOperatorL j E₀).inverse‖ ≤ I)
    (hAx : (weakEnergyZeroOperatorL j (E₀+r • E₁ x+r^2 • E₂ x)).IsInvertible)
    (hIx : ‖(weakEnergyZeroOperatorL j (E₀+r • E₁ x+r^2 • E₂ x)).inverse‖ ≤ I)
    (hFlat : ∀ f v, E₀ (P₀ f) (j v) = 0) :
    LocalSmoothJetBudget (fun p => weakEnergyPoissonOperatorL j (E₀+r • E₁ p+r^2 • E₂ p) P₀-
      P₀) x N (weakEnergyPoissonDifferenceBudget j E₀ P₀ N C I*r) := by
  let U (p : P) := weakEnergyPoissonOperatorL j (E₀+r • E₁ p+r^2 • E₂ p) P₀
  let D := weakEnergyPoissonJetBudget j P₀ N C I
  let L := weakEnergyFirstVariationOperatorL j E₀ P₀
  have hR := localWeakEnergyPoissonTaylor_budget
    j E₀ E₁ E₂ P₀ x r N C I hr hr₁ hI hE₁ hE₂ hA₀ hI₀ hAx hIx hFlat
  have hSlope := ((hE₁.linear_postcomp L).const_smul r hr)
  have h := hR.add hSlope
  have hs : (fun p => U p-P₀-r • weakEnergyFirstVariationL j E₀ (E₁ p) P₀+r • (L ∘ E₁) p) =
      fun p => U p-P₀ := by
    funext p
    rw [Function.comp_apply,show L (E₁ p) = weakEnergyFirstVariationL j E₀ (E₁ p) P₀
      from weakEnergyFirstVariationOperatorL_apply _ _ _ _,sub_add_cancel]
  change LocalSmoothJetBudget (fun p => U p-P₀-r • weakEnergyFirstVariationL j E₀ (E₁ p) P₀+
    r • (L ∘ E₁) p) x N (D*r^2+r*(‖L‖*C)) at h
  rw [hs] at h
  apply h.enlarge
  change D*r^2+r*(‖L‖*C) ≤ (D+‖L‖*C)*r
  rcases hr.eq_or_lt with hZero | hPos
  · simp only [← hZero,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,add_zero,le_refl]
  have hD : 0 ≤ D := (mul_nonneg_iff_of_pos_right (sq_pos_of_pos hPos)).mp hR.nonneg
  have hSq : r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hr₁ hr]
  nlinarith only [mul_le_mul_of_nonneg_left hSq hD]

end CalderonN
