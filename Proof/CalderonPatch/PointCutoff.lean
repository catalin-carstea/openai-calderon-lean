module

public import Proof.CalderonPatch.FlatJetBounds
public import Mathlib.Analysis.InnerProductSpace.Defs

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- A function with zero jet through order `m` at the origin can be cut off
arbitrarily close to the origin with an arbitrarily small order-`m` norm.
The cutoff retains the germ of the original function. -/
theorem exists_small_cutoff_of_flatJet {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (hZero : ∀ j ≤ m, iteratedFDeriv ℝ j f 0 = 0)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ tsupport g ⊆ closedBall 0 R ∧
      g =ᶠ[𝓝 0] f ∧ ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ ε := by
  let χ : ContDiffBump (0 : E) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := χ.contDiff
  have hχCompact : HasCompactSupport (χ : E → ℝ) := by
    rw [HasCompactSupport, χ.tsupport_eq]
    exact isCompact_closedBall _ _
  obtain ⟨B, hB, hBC⟩ := hχCompact.exists_bound_iteratedFDeriv hχ m
  obtain ⟨ρ, hρ, C, hC, hCF⟩ := exists_flatJet_bound hf 0 m hZero
  let A : ℕ → ℝ := fun j => (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * (B * C)
  let D := 1 + ∑ j ∈ Finset.range (m + 1), A j
  have hA (j : ℕ) : 0 ≤ A j := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hAD (j : ℕ) (hj : j ≤ m) : A j ≤ D := by
    have h := Finset.single_le_sum (f := A) (fun k _ => hA k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    dsimp [D]; linarith
  let r := min (min R ρ) (min 1 (ε / D))
  have hr : 0 < r := lt_min (lt_min hR hρ) (lt_min zero_lt_one (div_pos hε hD))
  have hrR : r ≤ R := (min_le_left _ _).trans (min_le_left _ _)
  have hrρ : r ≤ ρ := (min_le_left _ _).trans (min_le_right _ _)
  have hr₁ : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε / D := (min_le_right _ _).trans (min_le_right _ _)
  let c : E → ℝ := fun x => χ (r⁻¹ • x)
  let g : E → ℝ := fun x => c x * f x
  have hc : ContDiff ℝ ∞ c := hχ.comp (contDiff_id.const_smul _)
  have hg : ContDiff ℝ ∞ g := hc.mul hf
  have hscale (x : E) : ‖r⁻¹ • x‖ = r⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have hsupp : tsupport g ⊆ closedBall 0 r := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    have hxr : r < ‖x‖ := by simpa [mem_closedBall, dist_zero_right] using hn
    have hxo : χ.rOut ≤ dist (r⁻¹ • x) 0 := by
      rw [dist_zero_right, hscale]
      change 1 ≤ r⁻¹ * ‖x‖
      calc
        1 = r⁻¹ * r := (inv_mul_cancel₀ hr.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hxr.le (inv_nonneg.mpr hr.le)
    exact hx (by change χ (r⁻¹ • x) * f x = 0; rw [χ.zero_of_le_dist hxo, zero_mul])
  refine ⟨g, hg, hsupp.trans (closedBall_subset_closedBall hrR), ?_, ?_⟩
  · filter_upwards [ball_mem_nhds (0 : E) (show 0 < r / 2 by positivity)] with x hx
    change χ (r⁻¹ • x) * f x = f x
    have hc₁ : χ (r⁻¹ • x) = 1 := by
      apply χ.one_of_mem_closedBall
      rw [mem_closedBall, dist_zero_right, hscale]
      change r⁻¹ * ‖x‖ ≤ 1 / 2
      have hx' : ‖x‖ < r / 2 := by simpa [mem_ball, dist_zero_right] using hx
      calc
        _ ≤ r⁻¹ * (r / 2) := mul_le_mul_of_nonneg_left hx'.le (inv_nonneg.mpr hr.le)
        _ = 1 / 2 := by rw [← mul_div_assoc, inv_mul_cancel₀ hr.ne']
    rw [hc₁, one_mul]
  intro j hj x
  by_cases hx : x ∈ closedBall (0 : E) r
  · have hscaled (i : ℕ) (hi : i ≤ m) :
        ‖iteratedFDeriv ℝ i c x‖ ≤ (r⁻¹) ^ i * B := by
      have h := congrFun (iteratedFDeriv_comp_const_smul (f := (χ : E → ℝ))
        (i := i) r⁻¹ (hχ.of_le (by simp))) x
      change ‖iteratedFDeriv ℝ i (fun z => χ (r⁻¹ • z)) x‖ ≤ _
      rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hBC i hi _) (by positivity)
    have hbound : ‖iteratedFDeriv ℝ j g x‖ ≤ A j * r := calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ *
          ‖iteratedFDeriv ℝ (j - i) f x‖ := norm_iteratedFDeriv_mul_le hc hf x (by simp)
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (B * C) * r := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hpow : (r⁻¹) ^ i * r ^ (m + 1 - (j - i)) = r ^ (m + 1 - j) := by
          rw [show m + 1 - (j - i) = i + (m + 1 - j) by omega, pow_add,
            ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
        have hpowle : r ^ (m + 1 - j) ≤ r := by
          simpa only [pow_one] using pow_le_pow_of_le_one hr.le hr₁
            (show 1 ≤ m + 1 - j by omega)
        calc
          _ ≤ (j.choose i : ℝ) * ((r⁻¹) ^ i * B) * (C * r ^ (m + 1 - (j - i))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hscaled i (hij.trans hj)) (by positivity))
              (hCF r hr hrρ x hx (j - i) (by omega)) (norm_nonneg _) (by positivity)
          _ = (j.choose i : ℝ) * (B * C) * r ^ (m + 1 - j) := by
            rw [← hpow]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hpowle (by positivity)
      _ = A j * r := by simp only [Finset.sum_mul, A]
    exact hbound.trans ((mul_le_mul_of_nonneg_right (hAD j hj) hr.le).trans
      (by rwa [mul_comm, ← le_div_iff₀ hD]))
  · have hout : x ∉ Function.support (iteratedFDeriv ℝ j g) :=
      fun h => hx (hsupp (support_iteratedFDeriv_subset j h))
    rw [Function.notMem_support.mp hout, norm_zero]
    exact hε.le

end CalderonPatch
