module

public import Proof.CalderonN.FixedKernelIntegral

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Adapted from `SmoothLineDifference` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2000000

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Interval

namespace CalderonN

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The difference along a line, divided by the signed scale and
extended smoothly across scale zero. -/
@[expose] def smoothLineDifference (f : P → F) (q : P × (P × ℝ)) : F :=
  ∫ t in Icc (0 : ℝ) 1, fderiv ℝ f (q.1+(t*q.2.2) • q.2.1) q.2.1

theorem contDiff_smoothLineDifference {f : P → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothLineDifference f) := by
  let B := P × (P × ℝ)
  let J (q : ℝ × B) := fderiv ℝ f (q.2.1+(q.1*q.2.2.2) • q.2.2.1) q.2.2.1
  have hT : ContDiff ℝ ∞ (fun q : ℝ × B => q.2.1+(q.1*q.2.2.2) • q.2.2.1) :=
    contDiff_snd.fst.add ((contDiff_fst.mul contDiff_snd.snd.snd).smul contDiff_snd.snd.fst)
  have hJ : ContDiff ℝ ∞ J :=
    ((hf.fderiv_right (m := ∞) (by simp)).comp hT).clm_apply contDiff_snd.snd.fst
  let μ := (volume : Measure ℝ).restrict (Icc 0 1)
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).measure_lt_top.ne
  have hμ : μ (Icc 0 1)ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Icc.compl]
    simp
  apply contDiff_infty.mpr
  intro k
  apply contDiffOn_univ.mp
  exact contDiffOn_integral_on_compact (μ := μ) isCompact_Icc (subset_univ _)
    isOpen_univ isOpen_univ hμ k (fun t q => J (t,q)) (hJ.of_le (by simp)).contDiffOn

omit [FiniteDimensional ℝ P] in
theorem smul_smoothLineDifference {f : P → F} (hf : ContDiff ℝ ∞ f) (a v : P) (r : ℝ) :
    r • smoothLineDifference f (a,(v,r)) = f (a+r • v)-f a := by
  let Q (t : ℝ) := a+(t*r) • v
  let φ (t : ℝ) := f (Q t)
  let J (t : ℝ) := fderiv ℝ f (Q t) v
  have hQ (t : ℝ) : HasDerivAt Q (r • v) t := by
    simpa only [Q,id_eq,one_mul] using (((hasDerivAt_id t).mul_const r).smul_const v).const_add a
  have hφ (t : ℝ) : HasDerivAt φ (r • J t) t := by
    have h := ((hf.differentiable (by simp) (Q t)).hasFDerivAt.comp_hasDerivAt t (hQ t))
    rwa [map_smul] at h
  have hJ : Continuous J :=
    ((hf.fderiv_right (m := ∞) (by simp)).continuous.comp
      (continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const))).clm_apply
      continuous_const
  have hD : Continuous (fun t => r • J t) :=
    (continuous_const : Continuous (fun _ : ℝ => r)).smul hJ
  have h := intervalIntegral.integral_deriv_eq_sub' φ (funext fun t => (hφ t).deriv)
    (fun t _ => (hφ t).differentiableAt) hD.continuousOn (a := 0) (b := 1)
  rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,integral_smul] at h
  simpa only [smoothLineDifference,φ,Q,J,zero_mul,one_mul,zero_smul,add_zero] using h

end CalderonN
