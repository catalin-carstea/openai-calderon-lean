module

public import Proof.CalderonN.FourthDerivativeProductBounds

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/FourthBilinearVelocityBound.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace CalderonN

variable {P G H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma norm_iteratedFDeriv_linear_higher (v : P →L[ℝ] G) (x : P) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n+2) (v : P → G) x‖ = 0 := by
  have hD : fderiv ℝ (v : P → G) = fun _ => v := funext fun y => v.hasFDerivAt.fderiv
  rw [← norm_iteratedFDeriv_fderiv (n:=n+1),hD,iteratedFDeriv_const_of_ne (by omega)]
  simp

lemma norm_third_clm_apply_linear_le {Ω : Set P} (hΩ : IsOpen Ω)
    (A : P → G →L[ℝ] H) (hA : ContDiffOn ℝ ∞ A Ω) (v : P →L[ℝ] G) {x : P} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ 3 (fun p => A p (v p)) x‖ ≤
      3*‖iteratedFDeriv ℝ 2 A x‖*‖v‖+‖iteratedFDeriv ℝ 3 A x‖*‖v x‖ := by
  have hb := norm_iteratedFDerivWithin_clm_apply hA v.contDiff.contDiffOn hΩ.uniqueDiffOn hx (n:=3) (by simp)
  have hEqA (j : ℕ) : iteratedFDerivWithin ℝ j A Ω x = iteratedFDeriv ℝ j A x :=
    iteratedFDerivWithin_of_isOpen j hΩ hx
  have hEqV (j : ℕ) : iteratedFDerivWithin ℝ j (v : P → G) Ω x = iteratedFDeriv ℝ j (v : P → G) x :=
    iteratedFDerivWithin_of_isOpen j hΩ hx
  have hEqOut : iteratedFDerivWithin ℝ 3 (fun p => A p (v p)) Ω x =
      iteratedFDeriv ℝ 3 (fun p => A p (v p)) x := iteratedFDerivWithin_of_isOpen 3 hΩ hx
  have hN2 := norm_iteratedFDeriv_linear_higher v x 0
  have hN3 := norm_iteratedFDeriv_linear_higher v x 1
  simpa only [hEqA,hEqV,hEqOut,Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,show (3:ℕ).choose 2=3 from rfl,
    Nat.cast_ofNat,Nat.cast_one,Nat.sub_zero,Nat.reduceSub,norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,
    hN2,hN3,v.hasFDerivAt.fderiv,one_mul,mul_zero,zero_add,add_zero] using hb

lemma norm_fourth_clm_apply_linear_le {Ω : Set P} (hΩ : IsOpen Ω)
    (A : P → G →L[ℝ] H) (hA : ContDiffOn ℝ ∞ A Ω) (v : P →L[ℝ] G) {x : P} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ 4 (fun p => A p (v p)) x‖ ≤
      4*‖iteratedFDeriv ℝ 3 A x‖*‖v‖+‖iteratedFDeriv ℝ 4 A x‖*‖v x‖ := by
  have hb := norm_iteratedFDerivWithin_clm_apply hA v.contDiff.contDiffOn hΩ.uniqueDiffOn hx (n:=4) (by simp)
  have hEqA (j : ℕ) : iteratedFDerivWithin ℝ j A Ω x = iteratedFDeriv ℝ j A x :=
    iteratedFDerivWithin_of_isOpen j hΩ hx
  have hEqV (j : ℕ) : iteratedFDerivWithin ℝ j (v : P → G) Ω x = iteratedFDeriv ℝ j (v : P → G) x :=
    iteratedFDerivWithin_of_isOpen j hΩ hx
  have hEqOut : iteratedFDerivWithin ℝ 4 (fun p => A p (v p)) Ω x =
      iteratedFDeriv ℝ 4 (fun p => A p (v p)) x := iteratedFDerivWithin_of_isOpen 4 hΩ hx
  have hN2 := norm_iteratedFDeriv_linear_higher v x 0
  have hN3 := norm_iteratedFDeriv_linear_higher v x 1
  have hN4 := norm_iteratedFDeriv_linear_higher v x 2
  simpa only [hEqA,hEqV,hEqOut,Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,show (4:ℕ).choose 2=6 from rfl,show (4:ℕ).choose 3=4 from rfl,
    Nat.cast_ofNat,Nat.cast_one,Nat.sub_zero,Nat.reduceSub,norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,
    hN2,hN3,hN4,v.hasFDerivAt.fderiv,one_mul,mul_zero,zero_add,add_zero] using hb

/-- Applying a varying bilinear coefficient to the same linear velocity
    twice gives the fourth derivative budget C4 V^2+8 C3 V+12 C2. -/
theorem norm_fourth_bilinear_linear_velocity_le {Ω : Set P} (hΩ : IsOpen Ω)
    (A : P → G →L[ℝ] G →L[ℝ] H) (hA : ContDiffOn ℝ ∞ A Ω) (v : P →L[ℝ] G)
    {x : P} (hx : x ∈ Ω) (V C2 C3 C4 : ℝ) (hV : 0 ≤ V) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hv : ‖v‖ ≤ 1) (hVx : ‖v x‖ ≤ V)
    (hA2 : ‖iteratedFDeriv ℝ 2 A x‖ ≤ C2) (hA3 : ‖iteratedFDeriv ℝ 3 A x‖ ≤ C3)
    (hA4 : ‖iteratedFDeriv ℝ 4 A x‖ ≤ C4) :
    ‖iteratedFDeriv ℝ 4 (fun p => A p (v p) (v p)) x‖ ≤ C4*V^2+8*C3*V+12*C2 := by
  let B := fun p => A p (v p)
  have hB : ContDiffOn ℝ ∞ B Ω := hA.clm_apply v.contDiff.contDiffOn
  have hB3 : ‖iteratedFDeriv ℝ 3 B x‖ ≤ 3*C2+C3*V :=
    (norm_third_clm_apply_linear_le hΩ A hA v hx).trans (by
      calc
        _ ≤ 3*C2*1+C3*V := by gcongr
        _ = _ := by ring)
  have hB4 : ‖iteratedFDeriv ℝ 4 B x‖ ≤ 4*C3+C4*V :=
    (norm_fourth_clm_apply_linear_le hΩ A hA v hx).trans (by
      calc
        _ ≤ 4*C3*1+C4*V := by gcongr
        _ = _ := by ring)
  exact (norm_fourth_clm_apply_linear_le hΩ B hB v hx).trans (by
    calc
      _ ≤ 4*(3*C2+C3*V)*1+(4*C3+C4*V)*V := by gcongr
      _ = _ := by ring)

end CalderonN
