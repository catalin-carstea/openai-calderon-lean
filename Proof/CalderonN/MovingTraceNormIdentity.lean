module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-! The norm-comparison identity in Proposition 5.3. The form works on
a common invariant space for the physical and model operators. -/

public section

namespace CalderonN

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The full-adjoint norm expansion preserves the literal formal
lowering model and accounts for its difference from the model adjoint. -/
theorem movingTrace_norm_comparison_identity
    (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (hSym : ∀ x y, B x y = B y x)
    (T Td L U Ud : H →ₗ[ℝ] H)
    (hT : ∀ x y, B (T x) y = B x (Td y))
    (hU : ∀ x y, B (U x) y = B x (Ud y)) (x : H) :
    let Z := L-Td
    let v := (2 : ℝ) • T x+U x
    let w := (2 : ℝ) • L x+Ud x
    B v v-B w w =
      4*(B (T x) (T x)-B (L x) (L x)) +
        (2*B x (Td (U x)-U (Td x))+
         2*B x (Ud (T x)-T (Ud x))+
         B x (Ud (U x)-U (Ud x))-
         2*(B x (U (Z x))+B (U (Z x)) x)) := by
  dsimp only
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    map_add,map_sub,map_smul,smul_eq_mul]
  have hTd (a b : H) : B a (T b) = B (Td a) b := by
    rw [hSym a (T b),hT,hSym b (Td a)]
  have hUd (a b : H) : B a (U b) = B (Ud a) b := by
    rw [hSym a (U b),hU,hSym b (Ud a)]
  rw [← hT x (U x),← hU x (T x),← hU x (U x),
    hUd x (Td x),hTd x (Ud x),hUd x (Ud x),hUd x (L x),hU (L x) x,hU (Td x) x]
  rw [hSym (U x) (T x),hSym (Ud x) (Td x),hSym (Ud x) (L x)]
  ring

/-- Positivity of the complementary norm leaves the physical comparison
as soon as the commutator form is bounded. -/
theorem movingTrace_model_gap_le_of_error_form
    (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (hSym : ∀ x y, B x y = B y x)
    (hPos : ∀ x, 0 ≤ B x x)
    (T Td L U Ud : H →ₗ[ℝ] H)
    (hT : ∀ x y, B (T x) y = B x (Td y))
    (hU : ∀ x y, B (U x) y = B x (Ud y)) (x : H) (err : ℝ)
    (hErr :
      |2*B x (Td (U x)-U (Td x))+
       2*B x (Ud (T x)-T (Ud x))+
       B x (Ud (U x)-U (Ud x))-
       2*(B x (U ((L-Td) x))+B (U ((L-Td) x)) x)| ≤ err) :
    4*(B (T x) (T x)-B (L x) (L x)) ≤
      B ((2 : ℝ) • T x+U x) ((2 : ℝ) • T x+U x)+err := by
  have h := movingTrace_norm_comparison_identity B hSym T Td L U Ud hT hU x
  exact le_of_sub_nonneg (by linarith only [h,hPos ((2 : ℝ) • L x+Ud x),(abs_le.mp hErr).1])

end CalderonN
