module

public import Proof.CalderonN.FactoredPoissonJetBounds

import Mathlib.Tactic

/-! The normalized Poisson remainder after inclusion of the
zero-boundary correction into the solution space. -/

public section

noncomputable section
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open ShrinkingSpheres
variable {P E F U H : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem exists_uniform_affine_operator_inverse_near
    (A₀ : E →L[ℝ] F) (hA₀ : A₀.IsInvertible) (D : ℝ) (hD : 0 ≤ D) :
    ∃ η I : ℝ, 0 < η ∧ 0 ≤ I ∧ η ≤ 1 ∧ ‖A₀.inverse‖ ≤ I ∧
      ∀ r ∈ Set.Icc (0:ℝ) η, ∀ A₁ A₂ : E →L[ℝ] F, ‖A₁‖ ≤ D → ‖A₂‖ ≤ D →
      (A₀+r • A₁+r^2 • A₂).IsInvertible ∧ ‖(A₀+r • A₁+r^2 • A₂).inverse‖ ≤ I := by
  obtain ⟨δ,I,hδ,hI,hI₀,hInverse⟩ := exists_uniform_operator_inverse_near A₀ hA₀
  let η := min 1 (δ/(4*D+1))
  refine ⟨η,I,lt_min zero_lt_one (by positivity),hI,min_le_left _ _,hI₀,?_⟩
  intro r hr A₁ A₂ h₁ h₂
  have hr₁ : r ≤ 1 := hr.2.trans (min_le_left _ _)
  have hrδ : r*(4*D+1) ≤ δ := (le_div_iff₀ (by positivity)).mp (hr.2.trans (min_le_right _ _))
  have hSq : r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hr₁ hr.1]
  apply hInverse
  have hEq : A₀+r • A₁+r^2 • A₂-A₀ = r • A₁+r^2 • A₂ := by abel
  rw [hEq]
  calc
    _ ≤ ‖r • A₁‖+‖r^2 • A₂‖ := norm_add_le _ _
    _ ≤ r*D+r*D := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hr.1,abs_of_nonneg (sq_nonneg r)]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ hr.1)
        (mul_le_mul hSq h₂ (norm_nonneg _) hr.1)
    _ < δ := by
      have hHalf : r*(4*D+1)/2 ≤ δ/2 := by linarith only [hrδ]
      have hLe : r*D+r*D ≤ r*(4*D+1)/2 := by linarith only [hr.1]
      linarith only [hHalf,hLe,hδ]

@[expose] def liftedPoissonRemainderJetBudget (j : E →L[ℝ] U) (L : H →L[ℝ] U) (N : ℕ) (C I : ℝ) : ℝ :=
  let CI := I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*(2*C))^N)
  ‖j‖*poissonAffineRemainderJetBudget N CI I (2*C) C C L

theorem local_liftedPoissonRemainder_jet_budget
    (j : E →L[ℝ] U)
    (A₀ : E →L[ℝ] F) (T₀ : U →L[ℝ] F) (A₁ A₂ : P → E →L[ℝ] F) (T₁ T₂ : P → U →L[ℝ] F)
    (x : P) (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1)
    (N : ℕ) (C I : ℝ) (hC : 0 ≤ C) (hI : 0 ≤ I)
    (hA₀ : A₀.IsInvertible) (hI₀ : ‖A₀.inverse‖ ≤ I)
    (hA₁ : LocalSmoothJetBudget A₁ x N C) (hA₂ : LocalSmoothJetBudget A₂ x N C)
    (hT₁ : LocalSmoothJetBudget T₁ x N C) (hT₂ : LocalSmoothJetBudget T₂ x N C)
    (hA : (A₀+r • A₁ x+r^2 • A₂ x).IsInvertible)
    (hIA : ‖(A₀+r • A₁ x+r^2 • A₂ x).inverse‖ ≤ I)
    (L : H →L[ℝ] U) (hFlat : T₀.comp L = 0) :
    let A (p : P) := A₀+r • A₁ p+r^2 • A₂ p
    let T (p : P) := T₀+r • T₁ p+r^2 • T₂ p
    let Poisson (p : P) := L-j.comp ((A p).inverse.comp ((T p).comp L))
    let P₁ (p : P) := -(j.comp (A₀.inverse.comp ((T₁ p).comp L)))
    LocalSmoothJetBudget (fun p => Poisson p-L-r • P₁ p) x N
      (liftedPoissonRemainderJetBudget j L N C I*r^2) := by
  dsimp only
  let A (p : P) := A₀+r • A₁ p+r^2 • A₂ p
  let T (p : P) := T₀+r • T₁ p+r^2 • T₂ p
  let R (p : P) := (A p).inverse.comp ((T p).comp L)-r • A₀.inverse.comp ((T₁ p).comp L)
  let CI := I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*(2*C))^N)
  have hAs : ContDiffAt ℝ ∞ A x := (contDiffAt_const.add (hA₁.smooth.const_smul r)).add (hA₂.smooth.const_smul _)
  have hTs : ContDiffAt ℝ ∞ T x := (contDiffAt_const.add (hT₁.smooth.const_smul r)).add (hT₂.smooth.const_smul _)
  have hInv := hA.contDiffAt_map_inverse (n:=∞) |>.comp x hAs
  have hR : ContDiffAt ℝ ∞ R x :=
    (hInv.clm_comp (hTs.clm_comp contDiffAt_const)).sub
      ((contDiffAt_const.clm_comp (hT₁.smooth.clm_comp contDiffAt_const)).const_smul r)
  have hJ : LocalSmoothJetBudget R x N (poissonAffineRemainderJetBudget N CI I (2*C) C C L*r^2) := by
    refine ⟨hR,fun n hn => ?_⟩
    exact norm_iteratedFDeriv_factored_poisson_remainder_le A₀ T₀ A₁ A₂ T₁ T₂ x r hr hr₁
      N C I hC hI hA₀ hI₀ hA₁ hA₂ hT₁ hT₂ hA hIA L hFlat n hn
  have hEq : (fun p => L-j.comp ((A p).inverse.comp ((T p).comp L))-L-
      r • (-(j.comp (A₀.inverse.comp ((T₁ p).comp L))))) = fun p => -(j.comp (R p)) := by
    funext p
    ext b : 1
    simp only [R,sub_apply,smul_apply,neg_apply,ContinuousLinearMap.comp_apply,map_sub,map_smul]
    module
  change LocalSmoothJetBudget (fun p => L-j.comp ((A p).inverse.comp ((T p).comp L))-L-
      r • (-(j.comp (A₀.inverse.comp ((T₁ p).comp L))))) x N _
  rw [hEq]
  let Post := -((ContinuousLinearMap.compL ℝ H E U) j)
  have hPost : ‖Post‖ ≤ ‖j‖ := by
    rw [show ‖Post‖ = ‖(ContinuousLinearMap.compL ℝ H E U) j‖ by simp only [Post,norm_neg]]
    exact (((ContinuousLinearMap.compL ℝ H E U).le_opNorm j).trans
      (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_compL_le ℝ H E U)))
  have h := hJ.linear_postcomp Post
  have hPos := hJ.nonneg
  have hFun : Post ∘ R = fun p => -(j.comp (R p)) := by
    funext p
    simp only [Post,Function.comp_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.compL_apply]
  rw [← hFun]
  simpa only [liftedPoissonRemainderJetBudget,CI,← mul_assoc] using
    h.enlarge (mul_le_mul_of_nonneg_right hPost hPos)

end CalderonN
