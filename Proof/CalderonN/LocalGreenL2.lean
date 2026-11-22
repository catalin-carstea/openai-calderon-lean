module

public import Proof.CalderonN.GreenWeak

import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.SourceSobolev
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal

namespace CalderonN
open Elliptic
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
/-- The radius-power transfer from a separated test bound to the local L²
    norm, using an off-pole cutoff times the actual Green slice. -/
theorem offPoleLocalL2_of_separated_test_bound
    {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n}
    {G : X n × X n → ℝ} (hG : GreenGerm Ω g G)
    (hCover : closedBall (0 : X n) 1 ⊆ Ω)
    {N : ℝ} (hN : 0 < N)
    (hNtest : ∀ y ∈ closedBall (0 : X n) (1/4), ∀ x : X n, ∀ r ∈ Ioc (0:ℝ) (1/4),
      closedBall x r ⊆ closedBall (0 : X n) (1/2) → 2 * r ≤ dist x y →
      ∀ f : X n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → Function.support f ⊆ ball x r →
        |∫ z in ball (0 : X n) 1, G (z,y) * f z| ≤
          N * r ^ (2 - (n : ℝ) / 2) * (eLpNorm f 2 (volume.restrict (ball (0 : X n) 1))).toReal) :
    ∀ y ∈ closedBall (0 : X n) (1/4), ∀ x : X n, ∀ r ∈ Ioc (0:ℝ) (1/4),
      closedBall x r ⊆ closedBall (0 : X n) (1/2) → 2 * r ≤ dist x y →
      IntegrableOn (fun z => G (z,y)^2) (ball x (r/2)) ∧
      (∫ z in ball x (r/2), G (z,y)^2) ≤ N^2 * r ^ (4 - (n : ℝ)) := by
  let B := ball (0 : X n) 1
  let μ := (volume : Measure (X n)).restrict B
  intro y hy x r hr hSub hSep'
  have hSep : r < dist x y := by linarith [hr.1]
  have hBO : B ⊆ Ω := (ball_subset_closedBall : B ⊆ closedBall (0 : X n) 1).trans hCover
  have hSmall : closedBall (0 : X n) (1/2) ⊆ B := closedBall_subset_ball (by norm_num)
  have hyΩ := hBO (hSmall ((closedBall_subset_closedBall (by norm_num)) hy))
  have hC : closedBall x r ⊆ Ω \ {y} := by
    intro z hz
    refine ⟨hBO (hSmall (hSub hz)),?_⟩
    intro hz'
    have hzy : z = y := hz'
    have h := mem_closedBall.mp hz
    rw [hzy,dist_comm] at h
    exact hSep.not_ge h
  let χ : ContDiffBump x := ⟨r/2,r,half_pos hr.1,half_lt_self hr.1⟩
  let f (z : X n) := χ z*G (z,y)
  have hc : ContDiffOn ℝ ∞ (fun z => G (z,y)) (Ω \ {y}) :=
    hG.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hz => ⟨hz.1,hyΩ,hz.2⟩)
  have hF : ContDiff ℝ ∞ f := contDiff_mul_of_tsupport_subset (hΩ.sdiff isClosed_singleton)
    χ.contDiff ((χ.tsupport_eq ▸ hC)) hc
  have hFS : Function.support f ⊆ ball x r := by
    intro z hz
    have hχ : χ z ≠ 0 := fun hz' => hz (by simp [f,hz'])
    exact χ.support_eq ▸ hχ
  have hFK : HasCompactSupport f := χ.hasCompactSupport.mono
    (fun z hz hz' => hz (by simp [f,show χ z = 0 from hz']))
  have hBallB : ball x r ⊆ B := ball_subset_closedBall.trans (hSub.trans hSmall)
  have hTest := hNtest y hy x r hr hSub hSep' f hF hFK hFS
  let F (z : X n) := χ z*(G (z,y))^2
  let S := ∫ z, F z ∂μ
  have hFcompact : HasCompactSupport F := χ.hasCompactSupport.mono
    (fun z hz hz' => hz (by simp [F,show χ z = 0 from hz']))
  have hFcont : Continuous F :=
    (contDiff_mul_of_tsupport_subset (hΩ.sdiff isClosed_singleton) χ.contDiff
      (χ.tsupport_eq ▸ hC) (hc.pow 2)).continuous
  have hFint : Integrable F μ := hFcont.integrable_of_hasCompactSupport hFcompact
  have hNonneg : ∀ z : X n, 0 ≤ F z := fun z => mul_nonneg (χ.nonneg (x := z)) (sq_nonneg _)
  have hS : 0 ≤ S := integral_nonneg hNonneg
  have hf₂ : MemLp f 2 μ := hF.continuous.memLp_of_hasCompactSupport hFK
  have hNorm : (eLpNorm f 2 μ).toReal ≤ Real.sqrt S := by
    rw [← sqrt_integral_norm_sq_eq_eLpNorm_toReal hf₂]
    apply Real.sqrt_le_sqrt
    apply integral_mono (by simpa only [Real.norm_eq_abs,sq_abs] using hf₂.integrable_sq) hFint
    intro z
    change ‖f z‖^2 ≤ F z
    rw [Real.norm_eq_abs,sq_abs]
    change (χ z*G (z,y))^2 ≤ χ z*G (z,y)^2
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    simpa only [pow_two,mul_one] using (mul_le_mul_of_nonneg_left (χ.le_one (x := z)) (χ.nonneg (x := z)))
  have hTest' : S ≤ N * r ^ (2 - (n : ℝ) / 2)*Real.sqrt S := by
    have h := hTest
    have he : (∫ z in B, G (z,y)*f z) = S := by
      apply integral_congr_ae
      filter_upwards with z
      unfold F f
      ring
    rw [he,abs_of_nonneg hS] at h
    exact h.trans (mul_le_mul_of_nonneg_left hNorm (mul_nonneg hN.le (Real.rpow_nonneg hr.1.le _)))
  have hBound : S ≤ N^2 * r ^ (4 - (n : ℝ)) := by
    by_cases h0 : S = 0
    · rw [h0]
      exact mul_nonneg (sq_nonneg N) (Real.rpow_nonneg hr.1.le _)
    have h := Real.sqrt_pos.mpr (lt_of_le_of_ne hS (Ne.symm h0))
    have hs := Real.sq_sqrt hS
    have hle : Real.sqrt S ≤ N * r ^ (2 - (n : ℝ) / 2) := by
      apply le_of_mul_le_mul_right _ h
      rw [← pow_two,hs]
      exact hTest'
    have hh := pow_le_pow_left₀ h.le hle 2
    rw [hs,mul_pow, ← Real.rpow_natCast (r ^ (2 - (n : ℝ) / 2)) 2,
      ← Real.rpow_mul hr.1.le] at hh
    have he : (2 - (n : ℝ) / 2) * 2 = 4 - (n : ℝ) := by ring
    simpa only [Nat.cast_ofNat, he] using hh
  let V := ball x (r/2)
  have hVB : V ⊆ B := (ball_subset_ball (half_lt_self hr.1).le).trans hBallB
  have hfOn : EqOn (fun z => G (z,y)^2) F V := by
    intro z hz
    have hz' : z ∈ closedBall x χ.rIn := ball_subset_closedBall hz
    simp [F,χ.one_of_mem_closedBall hz']
  have hOn : IntegrableOn (fun z => G (z,y)^2) V :=
    ((hFcont.integrable_of_hasCompactSupport (μ := volume) hFcompact).integrableOn (s := V)).congr_fun
      (fun z hz => (hfOn hz).symm) isOpen_ball.measurableSet
  refine ⟨hOn,?_⟩
  rw [setIntegral_congr_fun isOpen_ball.measurableSet hfOn]
  refine (setIntegral_mono_set (show IntegrableOn F B volume from hFint)
    (Eventually.of_forall hNonneg) hVB.eventuallyLE).trans hBound

end CalderonN
