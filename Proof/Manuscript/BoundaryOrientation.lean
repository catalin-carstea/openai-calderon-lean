module

public import Proof.Manuscript.Lemma81Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

public section

noncomputable section
open scoped ContDiff

namespace CalderonPaper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthogonal derivative that fixes a hyperplane and preserves its
inward side is the identity. -/
theorem orthogonal_eq_id_of_fixes_tangent
    (T : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (n : E)
    (hn : ∀ v, L v = inner ℝ n v) (hL : 0 < L n)
    (htan : ∀ v, L v = 0 → T v = v)
    (horth : ∀ v w, inner ℝ (T v) (T w) = inner ℝ v w)
    (hside : 0 ≤ L (T n)) : T = ContinuousLinearMap.id ℝ E := by
  let a := L (T n) / L n
  let d := T n - a • n
  have ha : 0 ≤ a := div_nonneg hside hL.le
  have hd : L d = 0 := by
    simp only [d, map_sub, map_smul, smul_eq_mul, a]
    field_simp
    simp
  have hd_n : inner ℝ n d = 0 := (hn d).symm.trans hd
  have hd_Tn : inner ℝ (T n) d = 0 := by
    rw [← htan d hd, horth]
    exact hd_n
  have hdd : inner ℝ d d = 0 := by
    change inner ℝ (T n - a • n) d = 0
    simp [inner_sub_left, real_inner_smul_left, hd_Tn, hd_n]
  have hpar : T n = a • n := sub_eq_zero.mp (inner_self_eq_zero.mp hdd)
  have hnorm : 0 < inner ℝ n n := (hn n) ▸ hL
  have hsq : a * a = 1 := by
    have h := horth n n
    rw [hpar, real_inner_smul_left, real_inner_smul_right] at h
    exact mul_right_cancel₀ hnorm.ne' (by simpa [mul_assoc] using h)
  have ha_one : a = 1 := by nlinarith
  have hTn : T n = n := by simpa [ha_one] using hpar
  apply ContinuousLinearMap.ext
  intro v
  let t := L v / L n
  have ht : L (v - t • n) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, t]
    field_simp
    simp
  have h := htan _ ht
  rw [map_sub, map_smul, hTn] at h
  change T v = v
  simpa only [sub_left_inj] using h

end CalderonPaper
