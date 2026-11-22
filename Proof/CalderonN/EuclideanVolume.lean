module

public import Proof.CalderonN.Coordinates
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic

public section

/- Affine change of variables from LocalGreenPointwise and ball-volume scaling
   from LocalizedSourcePointBound in the 3D Theorem 3.1 proof. -/
noncomputable section
open Set Metric MeasureTheory
open scoped Pointwise ENNReal

namespace CalderonN
variable {n : ℕ}

private theorem image_translate_ball_zero (x : X n) (r : ℝ) :
    (fun z => x+z) '' ball (0 : X n) r = ball x r := by
  ext z
  constructor
  · rintro ⟨v,hv,rfl⟩
    simpa [Metric.mem_ball,dist_eq_norm] using hv
  · intro hz
    refine ⟨z-x,?_,by change x+(z-x) = z; rw [add_comm,sub_add_cancel]⟩
    simpa [Metric.mem_ball,dist_eq_norm] using hz

theorem setIntegral_comp_affineChart_ball
    (f : X n → ℝ) (x : X n) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    (∫ z in ball (0 : X n) r, f (x + s • z)) =
      (s ^ n)⁻¹ * ∫ z in ball x (s*r), f z := by
  let T := Homeomorph.addLeft x
  let D := ball x (s*r)
  have hEq : T '' (s • ball (0 : X n) r) = D := by
    rw [_root_.smul_ball hs.ne',smul_zero,Real.norm_eq_abs,abs_of_pos hs]
    exact image_translate_ball_zero x (s*r)
  have hPre : T ⁻¹' D = s • ball (0 : X n) r := by
    rw [← hEq,preimage_image_eq _ T.injective]
  have hTrans : (∫ z in s • ball (0 : X n) r, f (x+z)) = ∫ z in D, f z := by
    have ht := (measurePreserving_add_left (volume : Measure (X n)) x).setIntegral_preimage_emb
      T.measurableEmbedding f D
    change (∫ z in T ⁻¹' D, f (x+z)) = _ at ht
    rw [hPre] at ht
    exact ht
  have hdim : Module.finrank ℝ (X n) = n := by simp
  change (∫ z in ball (0 : X n) r, (fun v => f (x+v)) (s • z)) = _
  rw [Measure.setIntegral_comp_smul_of_pos volume (fun v => f (x+v)) (ball (0 : X n) r) hs,
    hdim,hTrans,smul_eq_mul]

theorem volume_real_ball (hn : 0 < n) (y : X n) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (X n)).real (ball y r) =
      r ^ n * (volume : Measure (X n)).real (ball 0 1) := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [measureReal_def, Measure.addHaar_ball (volume : Measure (X n)) y hr.le,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  simp only [X, I, finrank_euclideanSpace, Fintype.card_fin, measureReal_def]

theorem volume_real_ball_one_div_power (hn : 0 < n) (y : X n) {r : ℝ} (hr : 0 < r) :
    ((volume : Measure (X n)).real (ball y r)) ^ (1 / (n : ℝ)) =
      r * ((volume : Measure (X n)).real (ball 0 1)) ^ (1 / (n : ℝ)) := by
  have hV : 0 ≤ (volume : Measure (X n)).real (ball 0 1) := by positivity
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [volume_real_ball hn y hr, Real.mul_rpow (pow_nonneg hr.le _) hV, ← Real.rpow_natCast,
    ← Real.rpow_mul hr.le, mul_one_div, div_self hn', Real.rpow_one]

/-- The L²-to-point step for a separated Green ball. The only analytic input
    besides the physical L² bound is the interior point estimate on the unit ball. -/
theorem abs_le_rpow_of_rescaled_L2_bound {f : X n → ℝ} (x : X n)
    {r C D : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hL : (∫ z in ball x (r / 2), f z ^ 2) ≤ C * r ^ (4 - (n : ℝ)))
    (hPoint : |f x| ≤ D * Real.sqrt (∫ z in ball (0 : X n) (1 / 2), f (x + r • z) ^ 2)) :
    |f x| ≤ D * Real.sqrt C * r ^ (2 - (n : ℝ)) := by
  have hscale : (r ^ n)⁻¹ * (C * r ^ (4 - (n : ℝ))) = C * r ^ (4 - 2 * (n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hr.le]
    calc
      _ = C * (r ^ (-(n : ℝ)) * r ^ (4 - (n : ℝ))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hr]
        exact congrArg (fun a : ℝ => C * r ^ a) (by ring)
  have hbound :
      (∫ z in ball (0 : X n) (1 / 2), f (x + r • z) ^ 2) ≤ C * r ^ (4 - 2 * (n : ℝ)) := by
    rw [setIntegral_comp_affineChart_ball (fun z => f z ^ 2) x hr, mul_one_div, ← hscale]
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  apply hPoint.trans
  calc
    _ ≤ D * Real.sqrt (C * r ^ (4 - 2 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbound) hD
    _ = _ := by
      rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (r ^ (4 - 2 * (n : ℝ))),
        ← Real.rpow_mul hr.le, mul_assoc]
      exact congrArg (fun a : ℝ => D * (Real.sqrt C * r ^ a)) (by ring)

end CalderonN
