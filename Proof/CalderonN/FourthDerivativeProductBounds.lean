module

public import Proof.CalderonN.ThirdDerivativeProductBounds

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/FourthDerivativeProductBounds.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace CalderonN

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_iteratedFDeriv_four_eq_nested (f : P → E) (y : P) :
    ‖iteratedFDeriv ℝ 4 f y‖ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n:=3),← norm_iteratedFDeriv_fderiv (n:=2),
    ← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]

/-- The third scalar/vector product estimate in an arbitrary parameter
    space, directly from mathlib's local higher product rule. -/
lemma norm_third_iteratedFDeriv_smul_at {Ω : Set P} (hΩ : IsOpen Ω) {f : P → ℝ} {g : P → E}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) {y : P} (hy : y ∈ Ω) :
    ‖iteratedFDeriv ℝ 3 (fun x => f x • g x) y‖ ≤
      |f y| *‖iteratedFDeriv ℝ 3 g y‖+3*‖fderiv ℝ f y‖*‖iteratedFDeriv ℝ 2 g y‖+
      3*‖iteratedFDeriv ℝ 2 f y‖*‖fderiv ℝ g y‖+‖iteratedFDeriv ℝ 3 f y‖*‖g y‖ := by
  have hb := norm_iteratedFDerivWithin_smul_le hf hg hΩ.uniqueDiffOn hy (n:=3) (by simp)
  have hEqF (j : ℕ) : iteratedFDerivWithin ℝ j f Ω y = iteratedFDeriv ℝ j f y :=
    iteratedFDerivWithin_of_isOpen j hΩ hy
  have hEqG (j : ℕ) : iteratedFDerivWithin ℝ j g Ω y = iteratedFDeriv ℝ j g y :=
    iteratedFDerivWithin_of_isOpen j hΩ hy
  have hEqProd : iteratedFDerivWithin ℝ 3 (fun x => f x • g x) Ω y =
      iteratedFDeriv ℝ 3 (fun x => f x • g x) y := iteratedFDerivWithin_of_isOpen 3 hΩ hy
  simpa only [hEqProd,hEqF,hEqG,Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,show (3:ℕ).choose 2=3 from rfl,
    Nat.cast_ofNat,Nat.cast_one,norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,
    Real.norm_eq_abs,Nat.sub_zero,Nat.reduceSub,one_mul,zero_add] using hb

/-- The fourth scalar product estimate keeps all five binomial terms,
    without requiring a special choice of coordinates in the parameter space. -/
lemma norm_fourth_iteratedFDeriv_mul_at {Ω : Set P} (hΩ : IsOpen Ω) {f g : P → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) {y : P} (hy : y ∈ Ω) :
    ‖iteratedFDeriv ℝ 4 (fun x => f x*g x) y‖ ≤
      |f y| *‖iteratedFDeriv ℝ 4 g y‖+4*‖fderiv ℝ f y‖*‖iteratedFDeriv ℝ 3 g y‖+
      6*‖iteratedFDeriv ℝ 2 f y‖*‖iteratedFDeriv ℝ 2 g y‖+
      4*‖iteratedFDeriv ℝ 3 f y‖*‖fderiv ℝ g y‖+‖iteratedFDeriv ℝ 4 f y‖* |g y| := by
  have hb := norm_iteratedFDerivWithin_mul_le hf hg hΩ.uniqueDiffOn hy (n:=4) (by simp)
  have hEq (h : P → ℝ) (j : ℕ) : iteratedFDerivWithin ℝ j h Ω y = iteratedFDeriv ℝ j h y :=
    iteratedFDerivWithin_of_isOpen j hΩ hy
  simpa only [hEq,Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,show (4:ℕ).choose 2=6 from rfl,show (4:ℕ).choose 3=4 from rfl,
    Nat.cast_ofNat,Nat.cast_one,norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,
    Real.norm_eq_abs,Nat.sub_zero,Nat.reduceSub,one_mul,zero_add] using hb

end CalderonN
