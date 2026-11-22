module

public import Proof.CalderonN.WeakEnergyOperatorFamily

import Mathlib.Tactic

/-! Finite parameter jets of the weak Dirichlet lift and its quadratic
Taylor remainder on the same native H1 space. -/

public section

noncomputable section
open ContinuousLinearMap
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open ShrinkingSpheres

variable {P H Z F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[expose] def weakEnergyFirstVariationL (j : Z →L[ℝ] H)
    (E₀ E₁ : H →L[ℝ] H →L[ℝ] ℝ) (P₀ : F →L[ℝ] H) : F →L[ℝ] H :=
  -(j.comp ((weakEnergyZeroOperatorL j E₀).inverse.comp ((weakEnergyTestOperatorL j E₁).comp P₀)))

@[expose] def weakEnergyPoissonJetBudget (j : Z →L[ℝ] H) (P₀ : F →L[ℝ] H) (N : ℕ) (C I : ℝ) : ℝ :=
  let D := max ‖weakEnergyZeroOperatorL j‖ ‖weakEnergyTestOperatorL j‖*C
  let CI := I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*(2*D))^N)
  ‖j‖*poissonAffineRemainderJetBudget N CI I (2*D) D D P₀

theorem localWeakEnergyPoissonTaylor_budget
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
      P₀-r • weakEnergyFirstVariationL j E₀ (E₁ p) P₀) x N
        (weakEnergyPoissonJetBudget j P₀ N C I*r^2) := by
  let S := weakEnergyZeroOperatorL j
  let T := weakEnergyTestOperatorL j
  let E (p : P) := E₀+r • E₁ p+r^2 • E₂ p
  let D := max ‖S‖ ‖T‖*C
  let CI := I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*(2*D))^N)
  let A₀ := S E₀
  let T₀ := T E₀
  let A := S ∘ E
  let B := T ∘ E
  let R (p : P) := (A p).inverse.comp ((B p).comp P₀)-
    r • A₀.inverse.comp ((T (E₁ p)).comp P₀)
  have hC := hE₁.nonneg
  have hD : 0 ≤ D := mul_nonneg ((norm_nonneg S).trans (le_max_left _ _)) hC
  have hS (p : P) : A p = A₀+r • S (E₁ p)+r^2 • S (E₂ p) := by simp only [A,E,A₀,Function.comp_apply,map_add,map_smul]
  have hT (p : P) : B p = T₀+r • T (E₁ p)+r^2 • T (E₂ p) := by simp only [B,E,T₀,Function.comp_apply,map_add,map_smul]
  have hA₁ := (hE₁.linear_postcomp S).enlarge (mul_le_mul_of_nonneg_right (le_max_left ‖S‖ ‖T‖) hC)
  have hA₂ := (hE₂.linear_postcomp S).enlarge (mul_le_mul_of_nonneg_right (le_max_left ‖S‖ ‖T‖) hC)
  have hT₁ := (hE₁.linear_postcomp T).enlarge (mul_le_mul_of_nonneg_right (le_max_right ‖S‖ ‖T‖) hC)
  have hT₂ := (hE₂.linear_postcomp T).enlarge (mul_le_mul_of_nonneg_right (le_max_right ‖S‖ ‖T‖) hC)
  have hA' : (A₀+r • (S ∘ E₁) x+r^2 • (S ∘ E₂) x).IsInvertible := by
    simp only [Function.comp_apply]
    rw [← hS x]
    exact hAx
  have hIA' : ‖(A₀+r • (S ∘ E₁) x+r^2 • (S ∘ E₂) x).inverse‖ ≤ I := by
    simp only [Function.comp_apply]
    rw [← hS x]
    exact hIx
  have hT₀ : T₀.comp P₀ = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousLinearMap.ext
    intro v
    change weakEnergyTestOperatorL j E₀ (P₀ f) v = 0
    rw [weakEnergyTestOperatorL_apply,hFlat]
  have hE : ContDiffAt ℝ ∞ E x := (contDiffAt_const.add (hE₁.smooth.const_smul r)).add (hE₂.smooth.const_smul _)
  have hAs : ContDiffAt ℝ ∞ A x := S.contDiff.contDiffAt.comp x hE
  have hBs : ContDiffAt ℝ ∞ B x := T.contDiff.contDiffAt.comp x hE
  have hIs := hAx.contDiffAt_map_inverse (n:=∞) |>.comp x hAs
  have hR : ContDiffAt ℝ ∞ R x :=
    (hIs.clm_comp (hBs.clm_comp contDiffAt_const)).sub
      ((contDiffAt_const.clm_comp (hT₁.smooth.clm_comp contDiffAt_const)).const_smul r)
  have hRJ (n : ℕ) (hn : n ≤ N) :
      ‖iteratedFDeriv ℝ n R x‖ ≤ poissonAffineRemainderJetBudget N CI I (2*D) D D P₀*r^2 := by
    have h := norm_iteratedFDeriv_factored_poisson_remainder_le A₀ T₀ (S ∘ E₁) (S ∘ E₂) (T ∘ E₁) (T ∘ E₂)
      x r hr hr₁ N D I hD hI hA₀ hI₀ hA₁ hA₂ hT₁ hT₂ hA' hIA' P₀ hT₀ n hn
    dsimp only at h
    simpa only [R,hS,hT,CI,Function.comp_apply] using h
  have hForm : (fun p => weakEnergyPoissonOperatorL j (E p) P₀-P₀-r • weakEnergyFirstVariationL j E₀ (E₁ p) P₀) =
      fun p => -(j.comp (R p)) := by
    funext p
    apply ContinuousLinearMap.ext
    intro f
    simp only [weakEnergyPoissonOperatorL,weakEnergyFirstVariationL,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,R,ContinuousLinearMap.neg_apply,A,B,S,T,Function.comp_apply,A₀,
      map_sub,map_smul]
    module
  change LocalSmoothJetBudget (fun p => weakEnergyPoissonOperatorL j (E p) P₀-P₀-r • weakEnergyFirstVariationL j E₀ (E₁ p) P₀)
    x N _
  rw [hForm]
  have hJ : ContDiffAt ℝ ∞ (fun p => j.comp (R p)) x := contDiffAt_const.clm_comp hR
  refine ⟨hJ.neg,fun n hn => ?_⟩
  rw [norm_iteratedFDeriv_neg_at _ x hJ n]
  exact (norm_iteratedFDeriv_operator_postcomp_fixed_le j R x hR n).trans
    ((mul_le_mul_of_nonneg_left (hRJ n hn) (norm_nonneg _)).trans_eq
      (by unfold weakEnergyPoissonJetBudget; dsimp only [CI,D,S,T]; ring))

end CalderonN
