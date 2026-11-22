module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

import Mathlib.Tactic

public section
noncomputable section
open scoped ContDiff

namespace CalderonPatch

/-- A monotone smooth truncation, flat around zero and equal to the
identity outside a shrinking interval. -/
@[expose] def capTraceCutoff (ε s : ℝ) : ℝ :=
  s * Real.smoothTransition (s ^ 2 / ε ^ 2 - 1)

theorem capTraceCutoff_contDiff (ε : ℝ) : ContDiff ℝ ∞ (capTraceCutoff ε) := by
  exact contDiff_id.mul (Real.smoothTransition.contDiff.comp
    (((contDiff_id.pow 2).div_const (ε ^ 2)).sub contDiff_const))

theorem capTraceCutoff_zero_of_abs_le {ε s : ℝ} (hε : 0 < ε) (hs : |s| ≤ ε) :
    capTraceCutoff ε s = 0 := by
  have hs₂ : s ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs s]
    exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have he : s ^ 2 / ε ^ 2 - 1 ≤ 0 :=
    sub_nonpos.mpr ((div_le_iff₀ (pow_pos hε _)).mpr (by simpa only [one_mul] using hs₂))
  simp only [capTraceCutoff,Real.smoothTransition.zero_of_nonpos he,mul_zero]

theorem capTraceCutoff_eq_of_two_mul_le_abs {ε s : ℝ} (hε : 0 < ε) (hs : 2 * ε ≤ |s|) :
    capTraceCutoff ε s = s := by
  have hs₂ : (2*ε) ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs s]
    exact pow_le_pow_left₀ (mul_nonneg (by norm_num) hε.le) hs 2
  have he : 1 ≤ s ^ 2 / ε ^ 2 - 1 := by
    have hh : (2 : ℝ) ≤ s ^ 2 / ε ^ 2 := (le_div_iff₀ (pow_pos hε _)).mpr (by nlinarith)
    linarith
  simp only [capTraceCutoff,Real.smoothTransition.one_of_one_le he,mul_one]

theorem capTraceCutoff_deriv_nonneg (ε s : ℝ) : 0 ≤ deriv (capTraceCutoff ε) s := by
  let x := s ^ 2 / ε ^ 2 - 1
  have hx : HasDerivAt (fun t : ℝ => t ^ 2 / ε ^ 2 - 1) (2*s / ε^2) s := by
    convert ((((hasDerivAt_id s).pow 2).div_const (ε^2)).sub_const 1) using 1 <;> simp
  have hSmooth : ContDiff ℝ ∞ (Real.smoothTransition : ℝ → ℝ) :=
    Real.smoothTransition.contDiff
  have ht : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    (hSmooth.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hd := (hasDerivAt_id s).mul (ht.comp s hx)
  rw [show deriv (capTraceCutoff ε) s = _ from hd.deriv]
  have h₀ := Real.smoothTransition.nonneg x
  have h₁ : 0 ≤ deriv Real.smoothTransition x := Real.smoothTransition.monotone.deriv_nonneg
  have h₂ : 0 ≤ deriv Real.smoothTransition x * (2 / ε^2) * s^2 := by positivity
  change 0 ≤ 1 * Real.smoothTransition x + s * (deriv Real.smoothTransition x * (2*s / ε^2))
  have hprod : s * (deriv Real.smoothTransition x * (2*s / ε^2)) =
      deriv Real.smoothTransition x * (2 / ε^2) * s^2 := by ring
  rw [one_mul,hprod]
  exact add_nonneg h₀ h₂

end CalderonPatch
