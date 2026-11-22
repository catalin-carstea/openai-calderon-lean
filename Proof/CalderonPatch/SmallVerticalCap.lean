module

public import Proof.CalderonPatch.VerticalCap
public import Mathlib.Analysis.InnerProductSpace.Defs

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith

public section

noncomputable section
open Metric Set
open scoped ContDiff

namespace CalderonPatch

/-- The pushed cap can be confined to any given tangential radius and
vertical thickness. Its touching patch is exactly the tangential ball. -/
theorem exists_small_vertical_cap_with_graph {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z] (z₀ : Z) {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ∃ (b : Z → ℝ) (e : (Z × ℝ) ≃ (Z × ℝ)),
      ContDiff ℝ ∞ b ∧ (∀ z, 0 ≤ b z ∧ b z < R) ∧ {z | 0 < b z} = ball z₀ a ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      EqOn e id (ball z₀ a ×ˢ Ioo (-R) R)ᶜ ∧
      (∀ z, e (z,0) = (z,b z)) ∧
      e '' (univ ×ˢ Ici (0 : ℝ)) = {p | b p.1 ≤ p.2} ∧
      e '' (univ ×ˢ Ioi (0 : ℝ)) = {p | b p.1 < p.2} ∧
      (∀ p, (e p).1 = p.1) ∧ (∀ z, e (z,-b z) = (z,0)) ∧
      ∀ z, StrictMono (fun t => (e (z,t)).2) := by
  let η : ContDiffBump (0 : ℝ) := ⟨R / 2, R, by positivity, by linarith⟩
  let β : ContDiffBump z₀ := ⟨a / 2, a, by positivity, by linarith⟩
  have hη : ContDiff ℝ ∞ (η : ℝ → ℝ) := η.contDiff
  have hηD : Continuous (deriv (η : ℝ → ℝ)) := hη.continuous_deriv (by simp)
  have hηc : HasCompactSupport (deriv (η : ℝ → ℝ)) := by
    change HasCompactSupport (fun t => fderiv ℝ (η : ℝ → ℝ) t 1)
    exact HasCompactSupport.fderiv_apply ℝ η.hasCompactSupport (1 : ℝ)
  obtain ⟨C, hC⟩ := hηD.norm.bddAbove_range_of_hasCompactSupport hηc.norm
  let c := min (R / 2) (1 / (2 * (|C| + 1)))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcC : c * |C| < 1 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (R / 2) (1 / (2 * (|C| + 1)))) (abs_nonneg C)
    change c * |C| ≤ _ at h
    apply h.trans_lt
    rw [← mul_div_right_comm, one_mul, div_lt_iff₀ (by positivity : 0 < 2 * (|C| + 1))]
    linarith [abs_nonneg C]
  let b : Z → ℝ := fun z => c * β z
  have hb : ContDiff ℝ ∞ b := contDiff_const.mul β.contDiff
  have hbBound (z : Z) : 0 ≤ b z ∧ b z ≤ c := by
    exact ⟨mul_nonneg hc.le β.nonneg, (mul_le_mul_of_nonneg_left β.le_one hc.le).trans_eq (mul_one c)⟩
  have hBpos : {z | 0 < b z} = ball z₀ a := by
    ext z
    constructor
    · intro hz
      change 0 < c * β z at hz
      have hβ : β z ≠ 0 := fun h => (ne_of_gt hz) (by rw [h, mul_zero])
      exact (show Function.support β = ball z₀ a from β.support_eq) ▸ hβ
    · intro hz
      exact mul_pos hc (β.pos_of_mem_ball hz)
  have hη0 : η 0 = 1 := η.one_of_mem_closedBall (mem_closedBall_self η.rIn_pos.le)
  have hηout (t : ℝ) (ht : R ≤ |t|) : η t = 0 :=
    η.zero_of_le_dist (by simpa [Real.dist_eq] using ht)
  have hDpos (z : Z) (t : ℝ) : 0 < 1 + b z * deriv (η : ℝ → ℝ) t := by
    have hd : |deriv (η : ℝ → ℝ) t| ≤ |C| :=
      (show ‖deriv (η : ℝ → ℝ) t‖ ≤ C from hC (mem_range_self t)).trans (le_abs_self _)
    have hAbs : |b z * deriv (η : ℝ → ℝ) t| < 1 := by
      rw [abs_mul, abs_of_nonneg (hbBound z).1]
      exact (mul_le_mul (hbBound z).2 hd (abs_nonneg _) hc.le).trans_lt hcC
    linarith [neg_abs_le (b z * deriv (η : ℝ → ℝ) t)]
  obtain ⟨e, he, hes, hesi, hHalf, hInt⟩ :=
    exists_vertical_cap_diffeomorph hb η.contDiff hη0 hR hηout hDpos
  refine ⟨b, e, hb, fun z => ⟨(hbBound z).1, (hbBound z).2.trans_lt
    ((min_le_left _ _).trans_lt (by linarith))⟩, hBpos, hes, hesi, ?_, ?_, hHalf, hInt, ?_, ?_, ?_⟩
  · rintro ⟨z,t⟩ hp
    rw [he]
    have hzero : b z * η t = 0 := by
      by_cases hz : z ∈ ball z₀ a
      · have ht : t ∉ Ioo (-R) R := fun ht => hp ⟨hz,ht⟩
        apply mul_eq_zero.mpr
        exact Or.inr (hηout t (not_lt.mp fun habs => ht (abs_lt.mp habs)))
      · apply mul_eq_zero.mpr
        apply Or.inl
        apply le_antisymm _ (hbBound z).1
        exact le_of_not_gt fun hbz => hz (hBpos ▸ hbz)
    simp [hzero]
  · intro z
    rw [he, hη0, mul_one, zero_add]
  · intro p
    rw [he]
  · intro z
    have hMem : -b z ∈ closedBall (0 : ℝ) η.rIn := by
      rw [mem_closedBall,Real.dist_eq,sub_zero,abs_neg,abs_of_nonneg (hbBound z).1]
      exact (hbBound z).2.trans (min_le_left _ _)
    rw [he,η.one_of_mem_closedBall hMem,mul_one,neg_add_cancel]
  · intro z
    apply strictMono_of_deriv_pos
    intro t
    have hDiff : HasDerivAt (fun v => (e (z,v)).2) (1 + b z * deriv (η : ℝ → ℝ) t) t := by
      simp only [he]
      exact (hasDerivAt_id t).add ((hη.differentiable (by simp) t).hasDerivAt.const_mul (b z))
    rw [hDiff.deriv]
    exact hDpos z t

theorem exists_small_vertical_cap {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z] (z₀ : Z) {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ∃ (b : Z → ℝ) (e : (Z × ℝ) ≃ (Z × ℝ)),
      ContDiff ℝ ∞ b ∧ (∀ z, 0 ≤ b z ∧ b z < R) ∧ {z | 0 < b z} = ball z₀ a ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      EqOn e id (ball z₀ a ×ˢ Ioo (-R) R)ᶜ ∧
      (∀ z, e (z,0) = (z,b z)) ∧
      e '' (univ ×ˢ Ici (0 : ℝ)) = {p | b p.1 ≤ p.2} ∧
      e '' (univ ×ˢ Ioi (0 : ℝ)) = {p | b p.1 < p.2} := by
  obtain ⟨b,e,hb,hBound,hPos,he,hei,hOff,hSeam,hHalf,hInt,_,_,_⟩ :=
    exists_small_vertical_cap_with_graph z₀ ha hR
  exact ⟨b,e,hb,hBound,hPos,he,hei,hOff,hSeam,hHalf,hInt⟩

end CalderonPatch
