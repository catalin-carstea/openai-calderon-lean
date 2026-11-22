module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped Interval InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem norm_image_sub_le_of_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f v : ℝ → E} {C : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (v t) t)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖v t‖ ≤ C) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖f t-f s‖ ≤ C*‖t-s‖ := by
  refine (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (v t))
    (fun u hu => (hf u hu).hasFDerivAt.hasFDerivWithinAt) (fun u hu => ?_) hs ht
  simpa using hC u hu

/-- A Jacobi field written in a parallel orthonormal frame is close in
value and first derivative to the affine interpolant of its endpoints
when its acceleration is pointwise bounded by a small multiple of its
value. This bound uses the unit time interval. -/
theorem jacobi_affine_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (J V A : ℝ → E) (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1/2)
    (hJ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt J (V t) t)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt V (A t) t)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ‖A t‖ ≤ ε * ‖J t‖) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖J t - ((1-t) • J 0 + t • J 1)‖ ≤ 2*ε*(‖J 0‖+‖J 1‖) ∧
      ‖V t - (J 1 - J 0)‖ ≤ 2*ε*(‖J 0‖+‖J 1‖) := by
  have h₀ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one,le_rfl⟩
  have hCJ : ContinuousOn J (Icc 0 1) := fun t ht => (hJ t ht).continuousAt.continuousWithinAt
  have hCV : ContinuousOn V (Icc 0 1) := fun t ht => (hV t ht).continuousAt.continuousWithinAt
  obtain ⟨tmax,htmax,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0,h₀⟩ hCJ.norm
  let S := ‖J tmax‖
  have hS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖J t‖ ≤ S := hmax ht
  have hSpos : 0 ≤ S := norm_nonneg _
  have hVcomp (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖V t - V s‖ ≤ ε*S := by
    have h := norm_image_sub_le_of_derivative_bound hV
      (fun u hu => (hA u hu).trans (mul_le_mul_of_nonneg_left (hS u hu) hε)) hs ht
    have hb : ‖t-s‖ ≤ 1 := by rw [Real.norm_eq_abs,abs_le]; constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
    exact h.trans (mul_le_of_le_one_right (mul_nonneg hε hSpos) hb)
  have hIV : IntervalIntegrable V volume 0 1 :=
    hCV.intervalIntegrable_of_Icc zero_le_one
  have hFTC : (∫ u in (0 : ℝ)..1, V u) = J 1-J 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hJ u (by simpa only [uIcc_of_le zero_le_one] using hu)) hIV
  have hVel (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖V t-(J 1-J 0)‖ ≤ ε*S := by
    have he : (∫ u in (0 : ℝ)..1, V t-V u) = V t-(J 1-J 0) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hIV,intervalIntegral.integral_const,
        hFTC,sub_zero,one_smul]
    rw [← he]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := ε*S)
      (f := fun u => V t - V u) (fun u hu => by
        have hu' : u ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hu
        exact hVcomp u t ⟨hu'.1.le,hu'.2⟩ ht)
    simpa using h
  let L (t : ℝ) := (1-t) • J 0 + t • J 1
  have hL (t : ℝ) : HasDerivAt L (J 1-J 0) t := by
    have hh : HasDerivAt (fun t : ℝ => 1-t) (-1) t := by
      convert (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t) using 1 <;> simp
    have hh' := (hh.smul_const (J 0)).fun_add ((hasDerivAt_id t).smul_const (J 1))
    simpa only [L,id_eq,neg_smul,one_smul,sub_eq_add_neg, add_comm] using hh'
  have hDiff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖J t-L t‖ ≤ ε*S := by
    have h := norm_image_sub_le_of_derivative_bound
      (f := fun t => J t - L t) (v := fun t => V t-(J 1-J 0))
      (fun u hu => (hJ u hu).fun_sub (hL u)) hVel h₀ ht
    have hzero : J 0-L 0 = 0 := by simp [L]
    rw [hzero,sub_zero,sub_zero] at h
    exact h.trans (mul_le_of_le_one_right (mul_nonneg hε hSpos) (by
      rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ht.2))
  have hLnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖L t‖ ≤ ‖J 0‖+‖J 1‖ := by
    unfold L
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [ht.2]),
      Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1]))
      (mul_le_of_le_one_left (norm_nonneg _) ht.2)
  have hBig : S ≤ ε*S + (‖J 0‖+‖J 1‖) := by
    calc
      S = ‖(J tmax-L tmax)+L tmax‖ := by rw [sub_add_cancel]
      _ ≤ ‖J tmax-L tmax‖ + ‖L tmax‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hDiff tmax htmax) (hLnorm tmax htmax)
  have hSbig : S ≤ 2*(‖J 0‖+‖J 1‖) := by nlinarith only [hBig,mul_le_mul_of_nonneg_right hε' hSpos]
  have hErr : ε*S ≤ 2*ε*(‖J 0‖+‖J 1‖) :=
    (mul_le_mul_of_nonneg_left hSbig hε).trans_eq (by ring)
  exact fun t ht => ⟨(hDiff t ht).trans hErr,(hVel t ht).trans hErr⟩

/-- The boundary index expression differs from the flat squared endpoint
difference by at most the quadratic Jacobi error. -/
theorem jacobi_boundaryForm_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J V A : ℝ → E) (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1/2)
    (hJ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt J (V t) t)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt V (A t) t)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ‖A t‖ ≤ ε * ‖J t‖) :
    ‖J 1-J 0‖^2-2*ε*(‖J 0‖+‖J 1‖)^2 ≤ ⟪V 1,J 1⟫_ℝ - ⟪V 0,J 0⟫_ℝ := by
  let W := J 1-J 0
  let C := 2*ε*(‖J 0‖+‖J 1‖)
  have h := jacobi_affine_error J V A ε hε hε' hJ hV hA
  have h0 : ‖V 0-W‖ ≤ C := (h 0 ⟨le_rfl,zero_le_one⟩).2
  have h1 : ‖V 1-W‖ ≤ C := (h 1 ⟨zero_le_one,le_rfl⟩).2
  have h₀ : ⟪V 0-W,J 0⟫_ℝ ≤ C*‖J 0‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
  have h₁ : -(C*‖J 1‖) ≤ ⟪V 1-W,J 1⟫_ℝ := by
    have hh := (abs_real_inner_le_norm (V 1-W) (J 1)).trans
      (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    exact (abs_le.mp hh).1
  have hFlat : ⟪W,J 1⟫_ℝ - ⟪W,J 0⟫_ℝ = ‖W‖^2 := by
    rw [← inner_sub_right]
    exact real_inner_self_eq_norm_sq _
  rw [inner_sub_left] at h₀ h₁
  rw [show 2*ε*(‖J 0‖+‖J 1‖)^2 = C*(‖J 0‖+‖J 1‖) by dsimp [C]; ring]
  change ‖W‖^2-C*(‖J 0‖+‖J 1‖) ≤ _
  rw [mul_add,← hFlat]
  linarith only [h₀,h₁]

end CalderonN
