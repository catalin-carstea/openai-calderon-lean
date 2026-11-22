module

public import Proof.CalderonN.FiberEnergy
public import Proof.CalderonN.CrossTensor

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem fiber_cutoff_square_bound (d : (Data dim)) (ψ : (Field dim)) (χ : (X dim) → ℝ) (y : (X dim))
    (hψ : MemLp (fun w : ↥(standardSphere dim) => ψ (y, frameVector d.frame y w)) 2 (sphereProbability dim)) :
    χ y ^ 2 * fiberSq d.frame y (fun w => ψ (y,w)) ≤
      2 * (fiberSq d.frame y (fun w => cutoffDensity χ ψ (y,w)) + χ y ^ 2) := by
  let u (w : ↥(standardSphere dim)) := ψ (y, frameVector d.frame y w)
  let v (w : ↥(standardSphere dim)) := cutoffDensity χ ψ (y, frameVector d.frame y w)
  have hv : MemLp v 2 (sphereProbability dim) := (hψ.sub (memLp_const 1)).const_mul (χ y : ℂ)
  have huI : Integrable (fun w => ‖u w‖^2) (sphereProbability dim) := hψ.norm.integrable_sq
  have hvI : Integrable (fun w => ‖v w‖^2) (sphereProbability dim) := hv.norm.integrable_sq
  have hn (w : ↥(standardSphere dim)) : (χ y : ℂ) * u w = v w + (χ y : ℂ) := by
    simp only [v, u, cutoffDensity]
    ring
  have hw (w : ↥(standardSphere dim)) : χ y^2 * ‖u w‖^2 ≤ 2 * (‖v w‖^2 + χ y^2) := by
    have he : χ y^2 * ‖u w‖^2 = ‖(χ y : ℂ) * u w‖^2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [he, hn]
    have ht := norm_add_le (v w) (χ y : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at ht
    have hp := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith only [hp, sq_abs (χ y), sq_nonneg (‖v w‖ - |χ y|)]
  have hi := integral_mono (huI.const_mul _) ((hvI.add (integrable_const (χ y ^ 2))).const_mul 2) hw
  rw [integral_const_mul, integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add hvI (integrable_const (χ y ^ 2)),
    integral_const, probReal_univ, one_smul] at hi
  simp only [fiberSq_eq_integral_norm_sq]
  exact hi

private theorem re_fiber_sq_le (d : (Data dim)) (ψ : (Field dim)) (y : (X dim))
    (hψ : MemLp (fun w : ↥(standardSphere dim) => ψ (y, frameVector d.frame y w)) 2 (sphereProbability dim)) :
    ∫ w : ↥(standardSphere dim), (ψ (y, frameVector d.frame y w)).re ^ 2 ∂(sphereProbability dim) ≤
      fiberSq d.frame y (fun w => ψ (y,w)) := by
  rw [fiberSq_eq_integral_norm_sq]
  have hre := Complex.reCLM.lipschitzWith.comp_memLp (map_zero Complex.reCLM) hψ
  refine integral_mono hre.integrable_sq hψ.norm.integrable_sq (fun w => ?_)
  rw [← sq_abs (Complex.re _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

/-- The source transfer identities and Taylor remainder give a squared
pointwise bound on the exact weighted paired difference. -/
theorem weighted_pair_sq_le_fiberEnergy
    (d : (Data dim)) (ψ : (Field dim)) (χ u₁ u₂ : (X dim) → ℝ) (y : (X dim)) (C m : ℝ)
    (hC : 0 ≤ C) (hm : 0 < m) (hr : 0 < d.radius y)
    (hψ : MemLp (fun w : ↥(standardSphere dim) => ψ (y, frameVector d.frame y w)) 2 (sphereProbability dim))
    (hz : MemLp (fun w : ↥(standardSphere dim) => d.expMap (y,d.radius y • frameVector d.frame y w))
      2 (sphereProbability dim))
    (hu : MemLp (fun w : ↥(standardSphere dim) => u₁ (d.expMap (y,d.radius y • frameVector d.frame y w)))
      2 (sphereProbability dim))
    (hconst : (∫ w : ↥(standardSphere dim), (ψ (y, frameVector d.frame y w)).re ∂(sphereProbability dim)) = 1)
    (hcoords : ∀ i : (I dim), (∫ w : ↥(standardSphere dim), (ψ (y, frameVector d.frame y w)).re *
      (d.expMap (y,d.radius y • frameVector d.frame y w)) i ∂(sphereProbability dim)) = y i)
    (htransfer : (∫ w : ↥(standardSphere dim), (ψ (y, frameVector d.frame y w)).re *
      u₁ (d.expMap (y,d.radius y • frameVector d.frame y w)) ∂(sphereProbability dim)) = u₂ y)
    (hTaylor : ∀ᵐ w : ↥(standardSphere dim) ∂(sphereProbability dim),
      |u₁ (d.expMap (y,d.radius y • frameVector d.frame y w)) -
        (u₁ y + fderiv ℝ u₁ y (d.expMap (y,d.radius y • frameVector d.frame y w) - y))| ≤
        C * (d.radius y)^2)
    (hE : m * fiberSq d.frame y (fun w => cutoffDensity χ ψ (y,w)) ≤
      sphereEnergyDensity d (cutoffDensity χ ψ) y) :
    (χ y * (u₂ y-u₁ y) / (d.radius y)^2)^2 ≤
      2*C^2 * (sphereEnergyDensity d (cutoffDensity χ ψ) y / m + χ y^2) := by
  let v (w : ↥(standardSphere dim)) := (ψ (y, frameVector d.frame y w)).re
  have hv : MemLp v 2 (sphereProbability dim) := Complex.reCLM.lipschitzWith.comp_memLp (map_zero _) hψ
  have h := two_power_moment_bound hv hz hu hconst hcoords htransfer hC hTaylor
  have hbound := h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (re_fiber_sq_le d ψ y hψ))
    (mul_nonneg hC (sq_nonneg _)))
  let S := fiberSq d.frame y (fun w => ψ (y,w))
  have hS : 0 ≤ S := fiberSq_nonneg _ _ _
  have hq : |(u₂ y-u₁ y) / (d.radius y)^2| ≤ C * Real.sqrt S := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hr), div_le_iff₀ (sq_pos_of_pos hr)]
    exact hbound.trans_eq (by ring)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hq 2
  rw [sq_abs, mul_pow, Real.sq_sqrt hS] at hsq
  have hi := mul_le_mul_of_nonneg_left hsq (sq_nonneg (χ y))
  have hcut := fiber_cutoff_square_bound d ψ χ y hψ
  have henergy : fiberSq d.frame y (fun w => cutoffDensity χ ψ (y,w)) ≤
      sphereEnergyDensity d (cutoffDensity χ ψ) y / m := by
    exact (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hE)
  have hcomb := mul_le_mul_of_nonneg_left
    (hcut.trans (mul_le_mul_of_nonneg_left (add_le_add_left henergy (χ y^2)) (by norm_num)))
    (sq_nonneg C)
  calc (χ y * (u₂ y-u₁ y) / (d.radius y)^2)^2
      = χ y^2 * ((u₂ y-u₁ y) / (d.radius y)^2)^2 := by rw [mul_div_assoc, mul_pow]
    _ ≤ χ y^2 * (C^2 * S) := hi
    _ = C^2 * (χ y^2 * S) := by ring
    _ ≤ 2*C^2 * (sphereEnergyDensity d (cutoffDensity χ ψ) y / m + χ y^2) :=
      hcomb.trans_eq (by ring)

end CalderonN
