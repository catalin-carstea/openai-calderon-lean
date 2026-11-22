/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-! From Proof/TauCeti/Analysis/Calculus/SegmentIncrement.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 


























public section

noncomputable section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}

 


theorem enorm_sub_le_lintegral_enorm_fderiv_apply (x h : E)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ u (x + t • h))
    (hc : ContinuousOn (fun t : ℝ => fderiv ℝ u (x + t • h) h) (Icc 0 1)) :
    ‖u (x + h) - u x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ := by
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun s : ℝ => u (x + s • h)) t := by
    intro t ht
    simpa [Function.comp_def] using (hd t ht).comp t
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => x + s • h) t)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin (fun s : ℝ => u (x + s • h)) (Icc 0 1) t =
        fderiv ℝ u (x + t • h) h := by
    intro t ht
    rw [(hline t ht).derivWithin ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt ht),
      (hd t ht).deriv_comp_add_smul]
  have hC1 : ContDiffOn ℝ 1 (fun s : ℝ => u (x + s • h)) (Icc 0 1) := by
    rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc zero_lt_one)]
    exact ⟨fun t ht => (hline t ht).differentiableWithinAt,
      hc.congr hderiv⟩
  have h01 := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hC1 zero_le_one
  calc
    ‖u (x + h) - u x‖ₑ ≤
        ∫⁻ t in Icc (0 : ℝ) 1,
          ‖derivWithin (fun s : ℝ => u (x + s • h)) (Icc 0 1) t‖ₑ := by
      simpa using h01
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ :=
      setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hderiv t ht]

 







theorem norm_sub_le_integral_norm_fderiv_along_segment
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (x y : E)
    (h : x = y ∨
      (x ≠ y ∧
        (∀ t ∈ Ioo (0 : ℝ) ‖x - y‖,
          DifferentiableAt ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))) ∧
        ContinuousOn (fun t : ℝ => u (x + t • (‖x - y‖⁻¹ • (y - x))))
          (Icc 0 ‖x - y‖) ∧
        IntervalIntegrable
          (fun t : ℝ => ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖)
          volume 0 ‖x - y‖)) :
    ‖u x - u y‖ ≤ ∫ t in (0 : ℝ)..‖x - y‖,
      ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖ := by
  rcases h with rfl | ⟨hxy, hd, hc, hBi⟩
  · simp
  let L : ℝ := ‖x - y‖
  let ω : E := L⁻¹ • (y - x)
  let γ : ℝ → E := fun t => x + t • ω
  have hL : 0 < L := by simp [L, norm_pos_iff.mpr (sub_ne_zero.mpr hxy)]
  have hω : L • ω = y - x := by
    simp [ω, hL.ne', smul_smul]
  have hω_norm : ‖ω‖ = 1 := by
    dsimp [ω]
    rw [norm_smul, norm_inv, norm_norm, norm_sub_rev y x,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]
  have hfc : ContinuousOn (fun t : ℝ => u (γ t)) (Icc 0 L) := by
    simpa [L, γ, ω] using hc
  have hfd : DifferentiableOn ℝ (fun t : ℝ => u (γ t)) (Ioo 0 L) := by
    intro t ht
    exact ((hd t ht).comp t
      (by fun_prop : DifferentiableAt ℝ γ t)).differentiableWithinAt
  have hfB : ∀ᵐ t : ℝ, t ∈ Ioo 0 L →
      ‖deriv (fun s : ℝ => u (γ s)) t‖ ≤ ‖fderiv ℝ u (γ t)‖ :=
    .of_forall fun t ht => by
      have hdu : DifferentiableAt ℝ u (x + t • ω) := by
        simpa [ω, L] using hd t ht
      have hderiv : deriv (fun s : ℝ => u (γ s)) t =
          fderiv ℝ u (γ t) ω := by
        simpa only [γ] using hdu.deriv_comp_add_smul
      rw [hderiv]
      simpa only [hω_norm, mul_one] using
        (ContinuousLinearMap.le_opNorm (fderiv ℝ u (γ t)) ω)
  have hkey := norm_sub_le_integral_of_norm_deriv_le_of_le hL.le hfc hfd hfB hBi
  have hγL : γ L = y := by
    dsimp [γ]
    rw [hω, add_sub_cancel]
  have hγ0 : γ 0 = x := by simp [γ]
  rw [hγL, hγ0] at hkey
  rw [norm_sub_rev]
  simpa only [L, γ, ω] using hkey

end TauCeti
