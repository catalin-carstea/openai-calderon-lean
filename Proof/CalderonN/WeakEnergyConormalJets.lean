module

public import Proof.CalderonN.WeakEnergyPoissonJets
public import Proof.CalderonN.WeakConormalTaylorBound

import Proof.CalderonN.FiniteJetBudgetAlgebra
import Mathlib.Tactic

/-! Mixed jets of the weak conormal Taylor error, retaining the
flat harmonic cancellation in the test slot. -/

public section

noncomputable section
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open ShrinkingSpheres
variable {P H F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace LocalSmoothJetBudget
variable {f g : P → V} {x : P} {N : ℕ} {A B : ℝ}

theorem add (hf : LocalSmoothJetBudget f x N A) (hg : LocalSmoothJetBudget g x N B) :
    LocalSmoothJetBudget (fun p => f p+g p) x N (A+B) :=
  ⟨hf.smooth.add hg.smooth,fun n hn =>
    (norm_iteratedFDeriv_add_at_le f g x hf.smooth hg.smooth n).trans (add_le_add (hf.bound n hn) (hg.bound n hn))⟩

theorem const_smul (hf : LocalSmoothJetBudget f x N A) (r : ℝ) (hr : 0 ≤ r) :
    LocalSmoothJetBudget (fun p => r • f p) x N (r*A) := by
  refine ⟨hf.smooth.const_smul r,fun n hn => ?_⟩
  rw [norm_iteratedFDeriv_const_smul_at _ x hf.smooth,abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left (hf.bound n hn) hr

end LocalSmoothJetBudget

@[expose] def weakConormalBilinearL (P₀ : F →L[ℝ] H) :
    (H →L[ℝ] H →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] H) →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ F H (F →L[ℝ] ℝ)).comp
    ((ContinuousLinearMap.compL ℝ H (H →L[ℝ] ℝ) (F →L[ℝ] ℝ))
      ((ContinuousLinearMap.compL ℝ F H ℝ).flip P₀))

theorem weakConormalBilinearL_apply (P₀ : F →L[ℝ] H)
    (E : H →L[ℝ] H →L[ℝ] ℝ) (U : F →L[ℝ] H) (f g : F) :
    weakConormalBilinearL P₀ E U f g = E (U f) (P₀ g) := by
  simp only [weakConormalBilinearL,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]

theorem weakConormalBilinearL_eq (P₀ : F →L[ℝ] H)
    (E : H →L[ℝ] H →L[ℝ] ℝ) (U : F →L[ℝ] H) :
    weakConormalBilinearL P₀ E U = E.bilinearComp U P₀ := by
  ext f g : 2
  rw [weakConormalBilinearL_apply,ContinuousLinearMap.bilinearComp_apply]

theorem localWeakConormalTaylor_budget
    (E₀ : H →L[ℝ] H →L[ℝ] ℝ) (E₁ E₂ : P → H →L[ℝ] H →L[ℝ] ℝ)
    (U₀ : F →L[ℝ] H) (U : P → F →L[ℝ] H)
    (x : P) (r : ℝ) (N : ℕ) (A B : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1)
    (hE₁ : LocalSmoothJetBudget E₁ x N A) (hE₂ : LocalSmoothJetBudget E₂ x N A)
    (hU : LocalSmoothJetBudget (fun p => U p-U₀) x N (B*r))
    (hFlat : ∀ p, E₀.bilinearComp (U p-U₀) U₀ = 0) :
    LocalSmoothJetBudget (fun p => (E₀+r • E₁ p+r^2 • E₂ p).bilinearComp (U p) U₀-
      E₀.bilinearComp U₀ U₀-r • (E₁ p).bilinearComp U₀ U₀) x N
        (((2:ℝ)^N*‖weakConormalBilinearL U₀‖*(2*A*B)+
          ‖(weakConormalBilinearL U₀).flip U₀‖*A)*r^2) := by
  let C := weakConormalBilinearL U₀
  let E (p : P) := r • E₁ p+r^2 • E₂ p
  have hE : LocalSmoothJetBudget E x N (2*A*r) := by
    have h := (hE₁.const_smul r hr).add (hE₂.const_smul (r^2) (sq_nonneg r))
    have hSq : r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hr₁ hr]
    apply h.enlarge
    calc
      r*A+r^2*A ≤ r*A+r*A := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hSq hE₁.nonneg)
      _ = 2*A*r := by ring
  have hForm : (fun p => (E₀+r • E₁ p+r^2 • E₂ p).bilinearComp (U p) U₀-
      E₀.bilinearComp U₀ U₀-r • (E₁ p).bilinearComp U₀ U₀) =
      fun p => C (E p) (U p-U₀)+r^2 • C (E₂ p) U₀ := by
    funext p
    ext f g : 2
    have h := congrArg (fun T : F →L[ℝ] F →L[ℝ] ℝ => T f g) (hFlat p)
    simp only [ContinuousLinearMap.bilinearComp_apply,sub_apply,zero_apply,map_sub] at h
    simp only [C,E,weakConormalBilinearL_apply,ContinuousLinearMap.bilinearComp_apply,
      sub_apply,smul_apply,add_apply,map_sub,smul_eq_mul]
    linarith only [h]
  rw [hForm]
  have hFirst := hE.bilinear hU C
  have hSecond := (hE₂.linear_postcomp (C.flip U₀)).const_smul (r^2) (sq_nonneg r)
  have h := hFirst.add hSecond
  simpa only [Function.comp_apply,ContinuousLinearMap.flip_apply,C,
    show (2:ℝ)^N*‖C‖*(2*A*r)*(B*r)+r^2*(‖C.flip U₀‖*A) =
      ((2:ℝ)^N*‖C‖*(2*A*B)+‖C.flip U₀‖*A)*r^2 by ring] using h

end CalderonN
