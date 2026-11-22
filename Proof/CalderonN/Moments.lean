module

public import Proof.CalderonN.Coercivity

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace CalderonN

variable {n : ℕ}

instance [NeZero n] : IsProbabilityMeasure (sphereProbability n) where
  measure_univ := by
    let μ := (volume : Measure (X n)).toSphere
    have hμ : μ univ ≠ 0 := by
      rw [ne_eq, Measure.measure_univ_eq_zero]
      exact Measure.toSphere_ne_zero _
    change ((μ univ)⁻¹ • μ) univ = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hμ (measure_ne_top μ univ)]

private theorem integral_abs_le_sqrt_integral_sq {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {ψ : S → ℝ} (hψ : MemLp ψ 2 μ) :
    (∫ w, |ψ w| ∂μ) ≤ Real.sqrt (∫ w, (ψ w) ^ 2 ∂μ) := by
  have h₂ : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have h₁ : MemLp (fun _ : S => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two (h₂ ▸ hψ) h₁
  simpa only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs, one_pow,
    integral_const, probReal_univ, one_smul, Real.one_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_one] using h

/-- The affine part of the transfer cancels exactly. The density may
have either sign on the sphere. -/
theorem affine_moment_bound {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {ψ f affine : S → ℝ} {v₁ v₂ D : ℝ}
    (hψ : MemLp ψ 2 μ) (hf : MemLp f 2 μ) (haffine : MemLp affine 2 μ)
    (hrep : (∫ w, ψ w * affine w ∂μ) = v₁)
    (htransfer : (∫ w, ψ w * f w ∂μ) = v₂)
    (hD : 0 ≤ D) (herror : ∀ᵐ w ∂μ, |f w - affine w| ≤ D) :
    |v₂ - v₁| ≤ D * Real.sqrt (∫ w, (ψ w) ^ 2 ∂μ) := by
  have hprod₁ : Integrable (fun w => ψ w * f w) μ := hψ.integrable_mul hf
  have hprod₂ : Integrable (fun w => ψ w * affine w) μ := hψ.integrable_mul haffine
  have hdiff : (∫ w, ψ w * (f w - affine w) ∂μ) = v₂ - v₁ := by
    simp_rw [mul_sub]
    rw [integral_sub hprod₁ hprod₂, htransfer, hrep]
  have hmajor : Integrable (fun w => D * |ψ w|) μ := by
    have hψ' : Integrable ψ μ := hψ.integrable (by norm_num)
    exact hψ'.abs.const_mul D
  calc
    |v₂ - v₁| = ‖∫ w, ψ w * (f w - affine w) ∂μ‖ := by rw [hdiff, Real.norm_eq_abs]
    _ ≤ ∫ w, ‖ψ w * (f w - affine w)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ w, D * |ψ w| ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hmajor
      filter_upwards [herror] with w hw
      rw [Real.norm_eq_abs, abs_mul, mul_comm D]
      exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ ≤ D * Real.sqrt (∫ w, (ψ w) ^ 2 ∂μ) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq hψ) hD

private theorem affine_reproduction_of_coordinates {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {ψ : S → ℝ} {z : S → X n} {y : X n}
    (hψ : MemLp ψ 2 μ) (hz : MemLp z 2 μ)
    (hmass : (∫ w, ψ w ∂μ) = 1)
    (hcoords : ∀ i : I n, (∫ w, ψ w * z w i ∂μ) = y i)
    (b : ℝ) (L : X n →L[ℝ] ℝ) :
    (∫ w, ψ w * (b + L (z w - y)) ∂μ) = b := by
  have hψ' : Integrable ψ μ := hψ.integrable (by norm_num)
  have hprod : Integrable (fun w => ψ w • z w) μ :=
    memLp_one_iff_integrable.mp (hψ.smul hz)
  have hmoment : (∫ w, ψ w • z w ∂μ) = y := by
    ext i
    let P : X n →L[ℝ] ℝ := EuclideanSpace.proj i
    change P (∫ w, ψ w • z w ∂μ) = y i
    rw [← P.integral_comp_comm hprod]
    simp only [map_smul, smul_eq_mul]
    exact hcoords i
  have hconst : Integrable (fun w => ψ w • y) μ := hψ'.smul_const y
  have hcenter : Integrable (fun w => ψ w • (z w - y)) μ := by
    have he : (fun w => ψ w • (z w - y)) = (fun w => ψ w • z w) - (fun w => ψ w • y) := by
      funext w
      exact smul_sub (ψ w) (z w) y
    rw [he]
    exact hprod.sub hconst
  have hzero : (∫ w, ψ w • (z w - y) ∂μ) = 0 := by
    simp_rw [smul_sub]
    rw [integral_sub hprod hconst, hmoment, integral_smul_const, hmass, one_smul, sub_self]
  have hpoint (w : S) : ψ w * (b + L (z w - y)) =
      ψ w * b + L (ψ w • (z w - y)) := by
    rw [map_smul, smul_eq_mul, mul_add]
  simp_rw [hpoint]
  rw [integral_add (hψ'.mul_const b) (L.integrable_comp hcenter),
    integral_mul_const, hmass, one_mul, L.integral_comp_comm hcenter, hzero, map_zero, add_zero]

/-- The fiberwise estimate of Lemma 6.1. The endpoint samples and the
pair transfer use the same density and probability measure. -/
theorem two_power_moment_bound {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {ψ : S → ℝ} {z : S → X n} {y : X n}
    {u : X n → ℝ} {v C r : ℝ}
    (hψ : MemLp ψ 2 μ) (hz : MemLp z 2 μ) (hu : MemLp (fun w => u (z w)) 2 μ)
    (hmass : (∫ w, ψ w ∂μ) = 1)
    (hcoords : ∀ i : I n, (∫ w, ψ w * z w i ∂μ) = y i)
    (htransfer : (∫ w, ψ w * u (z w) ∂μ) = v) (hC : 0 ≤ C)
    (hTaylor : ∀ᵐ w ∂μ, |u (z w) - (u y + fderiv ℝ u y (z w - y))| ≤ C * r ^ 2) :
    |v - u y| ≤ C * r ^ 2 * Real.sqrt (∫ w, (ψ w) ^ 2 ∂μ) := by
  let L := fderiv ℝ u y
  have hL : MemLp (fun w => L (z w - y)) 2 μ :=
    L.lipschitzWith.comp_memLp (map_zero L) (hz.sub (memLp_const y))
  exact affine_moment_bound hψ hu ((memLp_const (u y)).add hL)
    (affine_reproduction_of_coordinates hψ hz hmass hcoords (u y) L) htransfer
    (mul_nonneg hC (sq_nonneg r)) hTaylor

end CalderonN
