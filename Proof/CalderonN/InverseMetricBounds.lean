module

public import Proof.CalderonN.MetricSmooth

import Mathlib.Tactic

@[expose] public section


noncomputable section
set_option autoImplicit false
open Set
namespace CalderonN
variable {n : ℕ}

lemma norm_axis (i : (I n)) : ‖axis i‖ = 1 := by simp [axis]

/-- A column of the inverse metric, interpreted as an ambient tangent vector. -/
def inverseMetricColumn (g : (MetricField n)) (y : (X n)) (j : (I n)) : (X n) :=
  WithLp.toLp 2 (fun i => (g y)⁻¹ i j)

lemma metricPair_inverseMetricColumn_self {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (j : (I n)) :
    metricPair g y (inverseMetricColumn g y j) (inverseMetricColumn g y j) =
      inverseMetricColumn g y j j := by
  have hm := Matrix.nonsing_inv_mul (g y) (isUnit_iff_ne_zero.mpr (h.posDef hK hy).det_pos.ne')
  have hcol (l : (I n)) : ∑ i, (g y)⁻¹ i j * g y i l = if j = l then 1 else 0 := by
    have hs (i : (I n)) : (g y)⁻¹ i j = (g y)⁻¹ j i := by
      have hinv : ((g y)⁻¹).transpose = (g y)⁻¹ := by
        rw [Matrix.transpose_nonsing_inv, (h.2 y hy).1]
      exact congrArg (fun M : (Mat n) => M j i) hinv
    simpa only [Matrix.mul_apply, Matrix.one_apply, hs] using congrArg (fun M : (Mat n) => M j l) hm
  change (∑ i, ∑ l, g y i l * (g y)⁻¹ i j * (g y)⁻¹ l j) = (g y)⁻¹ j j
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hcol' (l : (I n)) : (∑ i, g y i l * (g y)⁻¹ i j) = if j = l then 1 else 0 := by
    simpa only [mul_comm] using hcol l
  simp_rw [hcol']
  simp

lemma Elliptic.norm_inverseMetricColumn_le {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (j : (I n)) :
    ‖inverseMetricColumn g y j‖ ≤ K := by
  let v := inverseMetricColumn g y j
  have hl := (h.2 y hy).2 v |>.1
  rw [metricPair_inverseMetricColumn_self h hK hy j] at hl
  have hj : v j ≤ ‖v‖ := (le_abs_self _).trans (PiLp.norm_apply_le v j)
  have hh := mul_le_mul_of_nonneg_left hl hK.le
  have hrel : K*(K⁻¹*‖v‖^2) = ‖v‖^2 := by rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
  rw [hrel] at hh
  change ‖v‖ ≤ K
  have hsq : ‖v‖^2 ≤ K*‖v‖ := hh.trans (mul_le_mul_of_nonneg_left hj hK.le)
  nlinarith [norm_nonneg v]

/-- Ellipticity alone bounds every inverse coordinate entry by the same constant K. -/
theorem Elliptic.inverse_entry_bound {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (i j : (I n)) :
    |(g y)⁻¹ i j| ≤ K :=
  (PiLp.norm_apply_le (inverseMetricColumn g y j) i).trans (h.norm_inverseMetricColumn_le hK hy j)

/-- The actual orthonormal frame is bounded without a separate frame-size hypothesis. -/
theorem Elliptic.frame_norm_sq_bound {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (hframe : ∀ y ∈ Ω, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {y : (X n)} (hy : y ∈ Ω) (i : (I n)) : ‖e y i‖^2 ≤ K := by
  have hl := (h.2 y hy).2 (e y i) |>.1
  rw [hframe y hy i i, if_pos rfl] at hl
  have hh := mul_le_mul_of_nonneg_left hl hK.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul, mul_one] using hh

end CalderonN
