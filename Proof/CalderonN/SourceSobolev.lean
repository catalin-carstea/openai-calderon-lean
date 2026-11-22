module

public import Proof.CalderonN.Coordinates
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Tactic

public section

/- The critical-exponent volume loss in FixedBallSourceEnergy of the
   checked 3D proof, with the exponent determined by the dimension. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CalderonN

def criticalSobolevExponent (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 2))

variable {n : ℕ}

theorem criticalSobolevExponent_ne_top : criticalSobolevExponent n ≠ ⊤ := ENNReal.ofReal_ne_top

theorem criticalSobolevExponent_toReal (hn : 3 ≤ n) :
    (criticalSobolevExponent n).toReal = 2 * (n : ℝ) / ((n : ℝ) - 2) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact ENNReal.toReal_ofReal (div_nonneg (by positivity) (by linarith))

theorem two_le_criticalSobolevExponent (hn : 3 ≤ n) :
    (2 : ℝ≥0∞) ≤ criticalSobolevExponent n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← ENNReal.toReal_le_toReal (by simp) criticalSobolevExponent_ne_top,
    criticalSobolevExponent_toReal hn]
  norm_num
  exact (le_div_iff₀ (by linarith)).mpr (by linarith)

theorem criticalSobolevExponent_toReal_sub_inv (hn : 3 ≤ n) :
    1 / (2 : ℝ) - 1 / (criticalSobolevExponent n).toReal = 1 / (n : ℝ) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [criticalSobolevExponent_toReal hn]
  field_simp
  ring

theorem criticalSobolevExponent_inv_add (hn : 3 ≤ n) :
    (criticalSobolevExponent n)⁻¹ + (n : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
  have hq0 : criticalSobolevExponent n ≠ 0 :=
    (zero_lt_two.trans_le (two_le_criticalSobolevExponent hn)).ne'
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have h := criticalSobolevExponent_toReal_sub_inv hn
  simp only [one_div] at h
  linarith

/-- Hölder restriction to a finite measure, with the precise (1/n) loss
    from the critical Sobolev exponent. -/
theorem eLpNorm_two_toReal_le_volume_one_div_eLpNorm_critical (hn : 3 ≤ n)
    {A : Type*} [MeasurableSpace A] {f : A → ℝ} {μ ν : Measure A} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) (hf : MemLp f (criticalSobolevExponent n) μ) :
    (eLpNorm f 2 ν).toReal ≤
      (ν.real Set.univ) ^ (1 / (n : ℝ)) * (eLpNorm f (criticalSobolevExponent n) μ).toReal := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν)
    (two_le_criticalSobolevExponent hn) (hf.mono_measure hν).aestronglyMeasurable
  rw [ENNReal.toReal_ofNat, criticalSobolevExponent_toReal_sub_inv hn] at h
  have hLe : eLpNorm f 2 ν ≤ eLpNorm f (criticalSobolevExponent n) μ * ν Set.univ ^ (1 / (n : ℝ)) :=
    h.trans (by gcongr)
  have hTop : eLpNorm f (criticalSobolevExponent n) μ * ν Set.univ ^ (1 / (n : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top hf.ne (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _))
  have hReal := ENNReal.toReal_mono hTop hLe
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, measureReal_def, mul_comm] using hReal

theorem sqrt_integral_norm_sq_eq_eLpNorm_toReal
    {A F : Type*} [MeasurableSpace A] [NormedAddCommGroup F] {f : A → F} {μ : Measure A}
    (h : MemLp f 2 μ) :
    Real.sqrt (∫ z, ‖f z‖^2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),Real.sqrt_eq_rpow]
  norm_num [Real.rpow_two, ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg (fun _ => sq_nonneg _)) _)]

end CalderonN
