module

public import Proof.CalderonN.MetricCompatibility

import Proof.CalderonN.LocalFlowVariation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Derivative with respect to geodesic time in a smooth path family. -/
@[expose] def timeVelocity (q : ℝ × ℝ → (X dim)) (p : ℝ × ℝ) : (X dim) :=
  fderiv ℝ q p (0,1)

/-- Derivative in the variation parameter in the same path family. -/
@[expose] def pathVariation (q : ℝ × ℝ → (X dim)) (p : ℝ × ℝ) : (X dim) :=
  fderiv ℝ q p (1,0)

theorem hasDerivAt_geodesicTime {q : ℝ × ℝ → (X dim)} (h : DifferentiableAt ℝ q (s,t)) :
    HasDerivAt (fun b : ℝ => q (s,b)) (timeVelocity q (s,t)) t := by
  exact hasDerivAt_time_slice q s t h

theorem hasDerivAt_variation_slice {q : ℝ × ℝ → (X dim)} (h : DifferentiableAt ℝ q (s,t)) :
    HasDerivAt (fun a : ℝ => q (a,t)) (pathVariation q (s,t)) s := by
  have hI : HasDerivAt (fun a : ℝ => (a,t)) ((1,0) : ℝ × ℝ) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  exact h.hasFDerivAt.comp_hasDerivAt s hI

theorem contDiff_timeVelocity {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (timeVelocity q) :=
  (hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_pathVariation {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (pathVariation q) :=
  (hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem mixed_slice_deriv_eq {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q) (s t : ℝ) :
    pathVariation (timeVelocity q) (s,t) = timeVelocity (pathVariation q) (s,t) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ q) (s,t) :=
    (hq.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _
  unfold timeVelocity pathVariation
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simpa only [fderiv_const_apply,_root_.add_apply,zero_apply,ContinuousLinearMap.comp_apply,map_zero,
    zero_add,ContinuousLinearMap.flip_apply] using
    (hq.contDiffAt (x := (s,t))).isSymmSndFDerivAt (by simp) (1,0) (0,1)

private theorem eq_on_Icc_of_hasDerivAt_zero {f : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f 0 t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : f t = f 0 := by
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (f := f) (f' := fun _ => (0 : ℝ))
    (fun u hu => by
      rw [uIcc_of_le ht.1] at hu
      exact hf u ⟨hu.1,hu.2.trans ht.2⟩) intervalIntegrable_const
  exact sub_eq_zero.mp (by simpa using hI.symm)

/-- A geodesic in a smooth path family has constant metric speed on its
parameter interval. -/
theorem geodesic_squaredSpeed_eq_initial {U : Set (X dim)} (hU : IsOpen U)
    {g : (MetricField dim)} (hg : SmoothMetric U g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q) {s : ℝ}
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1,
      q (s,t) ∈ U ∧ timeVelocity (timeVelocity q) (s,t) =
        -connection g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    metricPair g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)) =
      metricPair g (q (s,0)) (timeVelocity q (s,0)) (timeVelocity q (s,0)) := by
  refine eq_on_Icc_of_hasDerivAt_zero
    (f := fun u => metricPair g (q (s,u)) (timeVelocity q (s,u)) (timeVelocity q (s,u)))
    (fun u hu => ?_) ht
  have hx := hasDerivAt_geodesicTime (hq.differentiable (by simp) (s,u))
  have hv := hasDerivAt_geodesicTime ((contDiff_timeVelocity hq).differentiable (by simp) (s,u))
  rw [(hpath u hu).2] at hv
  exact hasDerivAt_geodesic_squaredSpeed_zero hU hg (hpath u hu).1 hx hv

set_option maxHeartbeats 1300000 in
/-- First variation of half the squared speed for a smooth family of
geodesics on the unit time interval. The two boundary terms are the
endpoint velocities paired with the corresponding variations. -/
theorem geodesic_firstVariation
    {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)} (hg : SmoothMetric U g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (hfamily : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      q (s,t) ∈ U ∧ timeVelocity (timeVelocity q) (s,t) =
        -connection g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t))) :
    HasDerivAt (fun s => metricPair g (q (s,0)) (timeVelocity q (s,0)) (timeVelocity q (s,0))/2)
      (metricPair g (q (0,1)) (timeVelocity q (0,1)) (pathVariation q (0,1)) -
        metricPair g (q (0,0)) (timeVelocity q (0,0)) (pathVariation q (0,0))) 0 := by
  let v := timeVelocity q
  let J := pathVariation q
  let E (s t : ℝ) := metricPair g (q (s,t)) (v (s,t)) (v (s,t))/2
  let B (t : ℝ) := metricPair g (q (0,t)) (v (0,t)) (J (0,t))
  let d (t : ℝ) := metricPair g (q (0,t)) (v (0,t))
    (pathVariation v (0,t) + connection g (q (0,t)) (J (0,t)) (v (0,t)))
  have hqD (p : ℝ × ℝ) := hq.differentiable (by simp) p
  have hvD (p : ℝ × ℝ) := (contDiff_timeVelocity hq).differentiable (by simp) p
  have hJD (p : ℝ × ℝ) := (contDiff_pathVariation hq).differentiable (by simp) p
  have hzero : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have hcenter := hfamily.self_of_nhds
  have hconstant (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (fun s => E s t) =ᶠ[𝓝 (0 : ℝ)] fun s => E s 0 := by
    filter_upwards [hfamily] with s hs
    exact congrArg (fun b : ℝ => b/2) (geodesic_squaredSpeed_eq_initial hU hg hq hs ht)

  have hDs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => E s t) (d t) 0 := by
    have h := (hasDerivAt_metricPair hU hg (hcenter t ht).1
      (hasDerivAt_variation_slice (hqD (0,t))) (hasDerivAt_variation_slice (hvD (0,t)))
      (hasDerivAt_variation_slice (hvD (0,t)))).div_const 2
    have he : metricPair g (q (0,t))
        (pathVariation v (0,t) + connection g (q (0,t)) (J (0,t)) (v (0,t))) (v (0,t)) = d t :=
      metricPair_comm (hg.2 _ (hcenter t ht).1) _ _
    change HasDerivAt (fun s => E s t)
      ((metricPair g (q (0,t))
        (pathVariation v (0,t) + connection g (q (0,t)) (J (0,t)) (v (0,t))) (v (0,t)) + d t)/2) 0 at h
    rw [he,add_self_div_two] at h
    exact h
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : d t = d 0 :=
    ((hDs t ht).congr_of_eventuallyEq (hconstant t ht).symm).unique (hDs 0 hzero)
  have hBt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt B (d 0) t := by
    have h := hasDerivAt_metricPair hU hg (hcenter t ht).1
      (hasDerivAt_geodesicTime (hqD (0,t))) (hasDerivAt_geodesicTime (hvD (0,t)))
      (hasDerivAt_geodesicTime (hJD (0,t)))
    have hΓ := connection_comm hU hg (hcenter t ht).1 (v (0,t)) (J (0,t))
    have hMix : timeVelocity J (0,t) = pathVariation v (0,t) := (mixed_slice_deriv_eq hq 0 t).symm
    change HasDerivAt B
      (metricPair g (q (0,t)) (timeVelocity v (0,t) + connection g (q (0,t)) (v (0,t)) (v (0,t))) (J (0,t)) +
        metricPair g (q (0,t)) (v (0,t))
          (timeVelocity J (0,t) + connection g (q (0,t)) (v (0,t)) (J (0,t)))) t at h
    rw [show timeVelocity v (0,t) = _ from (hcenter t ht).2,neg_add_cancel,hΓ,hMix] at h
    have hnull : metricPair g (q (0,t)) 0 (J (0,t)) = 0 := by simp [metricPair]
    rw [hnull,zero_add] at h
    change HasDerivAt B (d t) t at h
    rwa [hd t ht] at h
  have he : B 1 - B 0 = d 0 := by
    have hT := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := B) (f' := fun _ => d 0)
      (a := (0 : ℝ)) (b := 1)
      (fun t ht => hBt t (by simpa only [uIcc_of_le zero_le_one] using ht))
      (intervalIntegrable_const)
    simpa using hT.symm
  have h₀ := hDs 0 hzero
  rw [← he] at h₀
  exact h₀

end CalderonN
