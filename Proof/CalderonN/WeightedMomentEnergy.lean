module

public import Proof.CalderonN.FiberEnergy
public import Proof.CalderonN.CrossTensor

import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Integrating the squared pointwise transfer bound in the literal chart
measure gives the weighted (L^2) estimate used by the continuation argument. -/
theorem weighted_moment_of_energy
    {Y : Set (X dim)} (hY : MeasurableSet Y)
    (d : (Data dim)) (ψ : (Field dim)) (χ q : (X dim) → ℝ)
    (C m B H : ℝ) (hm : 0 < m) (_hB : 0 ≤ B) (_hH : 0 ≤ H)
    (hEq : AEStronglyMeasurable q ((volume : Measure (X dim)).restrict Y))
    (hEint : IntegrableOn (sphereEnergyDensity d (cutoffDensity χ ψ)) Y)
    (hχint : IntegrableOn (fun y => χ y ^ 2) Y)
    (hχbound : (∫ y in Y, χ y ^ 2) ≤ H)
    (hEnorm : energyNorm Y d (cutoffDensity χ ψ) ≤ B)
    (hpoint : ∀ y ∈ Y,
      (m * fiberSq d.frame y (fun w => cutoffDensity χ ψ (y,w)) ≤ sphereEnergyDensity d (cutoffDensity χ ψ) y) ∧
      q y ^ 2 ≤ 2 * C^2 * (sphereEnergyDensity d (cutoffDensity χ ψ) y / m + χ y^2)) :
    eLpNorm q 2 ((volume : Measure (X dim)).restrict Y) ≤
      ENNReal.ofReal (Real.sqrt (2 * C^2 * (B^2 / m + H))) := by
  let E := sphereEnergyDensity d (cutoffDensity χ ψ)
  let G (y : (X dim)) := 2 * C^2 * (E y / m + χ y^2)
  have hG : IntegrableOn G Y := ((hEint.div_const m).add hχint).const_mul _
  have hpt : ∀ᵐ y ∂(volume : Measure (X dim)).restrict Y, q y^2 ≤ G y :=
    (ae_restrict_mem hY).mono fun y hy => (hpoint y hy).2
  have hq2 : IntegrableOn (fun y => q y^2) Y := by
    refine hG.mono' (hEq.pow 2) ?_
    filter_upwards [hpt] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (q y))] using hy
  have hLp : MemLp q 2 ((volume : Measure (X dim)).restrict Y) :=
    (memLp_two_iff_integrable_sq hEq).mpr hq2
  have hE0 : 0 ≤ ∫ y in Y, E y := by
    apply integral_nonneg_of_ae
    exact (ae_restrict_mem hY).mono fun y hy =>
      (mul_nonneg hm.le (fiberSq_nonneg _ _ _)).trans (hpoint y hy).1
  have hEbound : (∫ y in Y, E y) ≤ B^2 := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hEnorm 2
    change Real.sqrt (energySq Y d.γ d.frame d.radius (cutoffDensity χ ψ)) ^ 2 ≤ B^2 at hs
    rw [energySq_eq_integral_density Y d.γ d.frame d.radius _, Real.sq_sqrt hE0] at hs
    exact hs
  have hi := integral_mono_ae hq2 hG hpt
  have hI : (∫ y in Y, q y^2) ≤ 2 * C^2 * (B^2 / m + H) := by
    calc
      _ ≤ ∫ y in Y, G y := hi
      _ = 2 * C^2 * ((∫ y in Y, E y) / m + ∫ y in Y, χ y^2) := by
        unfold G
        rw [integral_const_mul, integral_add (hEint.div_const m) hχint, integral_div]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_right hEbound hm.le) hχbound) (by positivity)
  let Q := hLp.toLp q
  have hrep : (Q : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict Y] q := hLp.coeFn_toLp
  have hsq : ‖Q‖^2 = ∫ y in Y, q y^2 := by
    rw [← LocalMetricExtension.integral_sq_eq_norm_sq Q]
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx]
  have hnorm : ‖Q‖ ≤ Real.sqrt (2 * C^2 * (B^2 / m + H)) := by
    have hh := Real.sqrt_le_sqrt (hsq.trans_le hI)
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hh
  calc
    _ = eLpNorm (Q : (X dim) → ℝ) 2 ((volume : Measure (X dim)).restrict Y) := eLpNorm_congr_ae hrep.symm
    _ = ENNReal.ofReal ‖Q‖ := by rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top Q)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hnorm

end CalderonN
