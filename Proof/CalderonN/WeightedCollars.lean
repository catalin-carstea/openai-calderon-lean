module

public import Proof.CalderonN.Chart
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Tactic

@[expose] public section

/-! Adopted from `MixedKernelWeightedResidualV021` in anisotropic-calderon-lean
at revision `d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

noncomputable section

open Set MeasureTheory

namespace CalderonN.Elliptic

variable {dim : ℕ}
/-- WS: split of a Carleman inequality into the two collar terms, and the lower bound on
the closure of `O`; the weighted SQUARED estimate. -/
theorem weighted_sq_split {u L ψ wO : (X dim) → ℝ} {KB KH Ob : Set (X dim)} {τ C G hB hS hO : ℝ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hcarl : τ * G + τ ^ 3 * (∫ x, (Real.exp (τ * ψ x) * u x) ^ 2) ≤
      C * ∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2)
    (hu_int : Integrable (fun x => (Real.exp (τ * ψ x) * u x) ^ 2))
    (hL_int : Integrable (fun x => L x ^ 2))
    (hKB : MeasurableSet KB) (hKH : MeasurableSet KH) (hOm : MeasurableSet Ob)
    (hLzero : ∀ x, x ∉ KB ∪ KH → L x = 0)
    (hψB : ∀ x ∈ KB, ψ x ≤ hB) (hψS : ∀ x ∈ KH, ψ x ≤ hS) (hψO : ∀ x ∈ Ob, hO ≤ ψ x)
    (huO : ∀ x ∈ Ob, u x = wO x) (hwO_int : IntegrableOn (fun x => wO x ^ 2) Ob) :
    τ ^ 3 * (Real.exp (2 * (τ * hO)) * ∫ x in Ob, wO x ^ 2) ≤
      C * (Real.exp (2 * (τ * hB)) * (∫ x in KB, L x ^ 2) +
        Real.exp (2 * (τ * hS)) * ∫ x in KH, L x ^ 2) := by
  -- upper bound
  have hpt : ∀ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2 ≤
      Real.exp (2 * (τ * hB)) * KB.indicator (fun x => L x ^ 2) x +
        Real.exp (2 * (τ * hS)) * KH.indicator (fun x => L x ^ 2) x := by
    intro x
    have hiB : 0 ≤ KB.indicator (fun x => L x ^ 2) x :=
      Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
    have hiS : 0 ≤ KH.indicator (fun x => L x ^ 2) x :=
      Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
    have hB0 : 0 ≤ Real.exp (2 * (τ * hB)) * KB.indicator (fun x => L x ^ 2) x :=
      mul_nonneg (Real.exp_pos _).le hiB
    have hS0 : 0 ≤ Real.exp (2 * (τ * hS)) * KH.indicator (fun x => L x ^ 2) x :=
      mul_nonneg (Real.exp_pos _).le hiS
    by_cases hxB : x ∈ KB
    · have he : Real.exp (2 * (τ * ψ x)) ≤ Real.exp (2 * (τ * hB)) :=
        Real.exp_le_exp.mpr (by nlinarith [hψB x hxB])
      rw [Set.indicator_of_mem hxB]
      nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg (L x))]
    by_cases hxS : x ∈ KH
    · have he : Real.exp (2 * (τ * ψ x)) ≤ Real.exp (2 * (τ * hS)) :=
        Real.exp_le_exp.mpr (by nlinarith [hψS x hxS])
      rw [Set.indicator_of_mem hxS]
      nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg (L x))]
    · have hL0 : L x = 0 := hLzero x (fun h => h.elim hxB hxS)
      rw [hL0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact add_nonneg hB0 hS0
  have hBi : Integrable (fun x => Real.exp (2 * (τ * hB)) * KB.indicator (fun x => L x ^ 2) x) :=
    (hL_int.indicator hKB).const_mul _
  have hSi : Integrable (fun x => Real.exp (2 * (τ * hS)) * KH.indicator (fun x => L x ^ 2) x) :=
    (hL_int.indicator hKH).const_mul _
  have hup : (∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2) ≤
      Real.exp (2 * (τ * hB)) * (∫ x in KB, L x ^ 2) +
        Real.exp (2 * (τ * hS)) * ∫ x in KH, L x ^ 2 := by
    have hm : (∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2) ≤
        ∫ x, (Real.exp (2 * (τ * hB)) * KB.indicator (fun x => L x ^ 2) x +
          Real.exp (2 * (τ * hS)) * KH.indicator (fun x => L x ^ 2) x) :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg (L x)))
        (hBi.add hSi) (Filter.Eventually.of_forall hpt)
    rw [integral_add hBi hSi, integral_const_mul, integral_const_mul,
      integral_indicator hKB, integral_indicator hKH] at hm
    exact hm
  -- lower bound
  have hlowO : (∫ x in Ob, Real.exp (2 * (τ * hO)) * wO x ^ 2) ≤
      ∫ x in Ob, (Real.exp (τ * ψ x) * u x) ^ 2 := by
    refine setIntegral_mono_on (hwO_int.const_mul _) hu_int.integrableOn hOm fun x hx => ?_
    have he : Real.exp (2 * (τ * hO)) ≤ Real.exp (2 * (τ * ψ x)) :=
      Real.exp_le_exp.mpr (by nlinarith [hψO x hx])
    have e2 : (Real.exp (τ * ψ x) * u x) ^ 2 = Real.exp (2 * (τ * ψ x)) * wO x ^ 2 := by
      rw [huO x hx, mul_pow, ← Real.exp_nat_mul]
      norm_num
    rw [e2]
    exact mul_le_mul_of_nonneg_right he (sq_nonneg _)
  have hle : (∫ x in Ob, (Real.exp (τ * ψ x) * u x) ^ 2) ≤
      ∫ x, (Real.exp (τ * ψ x) * u x) ^ 2 :=
    setIntegral_le_integral hu_int (Filter.Eventually.of_forall fun x => sq_nonneg _)
  rw [integral_const_mul] at hlowO
  have hτ3 : 0 ≤ τ ^ 3 := pow_nonneg hτ 3
  have hτG : 0 ≤ τ * G := mul_nonneg hτ hG
  calc τ ^ 3 * (Real.exp (2 * (τ * hO)) * ∫ x in Ob, wO x ^ 2)
      ≤ τ ^ 3 * (∫ x, (Real.exp (τ * ψ x) * u x) ^ 2) :=
        mul_le_mul_of_nonneg_left (hlowO.trans hle) hτ3
    _ ≤ C * ∫ x, Real.exp (2 * (τ * ψ x)) * L x ^ 2 := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hup hC

end CalderonN.Elliptic
