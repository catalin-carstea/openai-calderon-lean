module

public import Proof.CalderonN.FixedBallGreenPairing

import Proof.CalderonN.CovariantHessian
import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter Set Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 1000000 in
/-- The energy identity gives uniqueness for classical harmonic functions
on the closed unit ball with the same boundary data. -/
theorem eqOn_closedUnitBall_of_laplace_eq_zero
    {U : Set (X dim)} (hU : IsOpen U) (hBU : closedBall (0 : (X dim)) 1 ⊆ U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {u : (X dim) → ℝ}
    (hu : ContDiffOn ℝ ∞ u U)
    (hLap : ∀ x ∈ ball (0 : (X dim)) 1, laplace g u x = 0)
    (hBdy : EqOn u 0 (standardSphere dim)) : EqOn u 0 (closedBall (0 : (X dim)) 1) := by
  let V (x : (X dim)) := u x • metricFluxVector g u x
  let W (x : (X dim)) := chartVolume g x * covectorSq g u x
  have hV : ContDiffOn ℝ ∞ V U := hu.smul (contDiffOn_metricFluxVector hU hg hu)
  have hW : ContinuousOn W U :=
    ((contDiffOn_metric_volume hg).mul (contDiffOn_covectorSq hU hg hu)).continuousOn
  obtain ⟨F,hF,hFEq⟩ := exists_global_extension_on_closedUnitBall hU hBU hV
  have hFlux : unitSphereFlux F = 0 := by
    unfold unitSphereFlux
    apply integral_eq_zero_of_ae
    filter_upwards with x
    rw [(hFEq x (sphere_subset_closedBall x.property)).eq_of_nhds]
    have hz : V x = 0 := by simp only [V,hBdy x.property,Pi.zero_apply,zero_smul]
    simp only [hz,inner_zero_right,Pi.zero_apply]
  have hDiv (x : (X dim)) (hx : x ∈ ball (0 : (X dim)) 1) : coordinateFluxDivergence F x = W x := by
    rw [coordinateFluxDivergence_congr_germ (hFEq x (ball_subset_closedBall hx))]
    have hxU := hBU (ball_subset_closedBall hx)
    have had (i : (I dim)) := ((contDiffOn_divergenceFlux hU hg hu i).differentiableOn
      (by simp)).differentiableAt (hU.mem_nhds hxU)
    have hud := (hu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
    have hp (i : (I dim)) : coordDeriv i (fun z => V z i) x =
        u x * coordDeriv i (fun z => divergenceFlux g u z i) x +
          coordDeriv i u x * divergenceFlux g u x i := by
      change coordDeriv i (fun z => u z * divergenceFlux g u z i) x = _
      simp only [coordDeriv, fderiv_fun_mul hud (had i),add_apply,smul_apply,smul_eq_mul]
      ring
    change (∑ i, coordDeriv i (fun z => V z i) x) = _
    simp_rw [hp]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,
      ← chartVolume_mul_laplace_eq_divergence hU hg hu hxU,hLap x hx,mul_zero,mul_zero,zero_add]
    simp only [W,covectorSq,divergenceFlux,divergenceCoeff,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hZ : (∫ x in ball (0 : (X dim)) 1, W x) = 0 := by
    calc
      _ = ∫ x in ball (0 : (X dim)) 1, coordinateFluxDivergence F x :=
        setIntegral_congr_fun measurableSet_ball (fun x hx => (hDiv x hx).symm)
      _ = _ := (integral_unitBall_coordinateFluxDivergence F hF).trans hFlux
  have hVolume (x : (X dim)) (hx : x ∈ U) : 0 < chartVolume g x :=
    Real.sqrt_pos.2 (hg.2 x hx).det_pos
  have hNon : ∀ᵐ x ∂(volume.restrict (ball (0 : (X dim)) 1)), 0 ≤ W x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hx' := hBU (ball_subset_closedBall hx)
    by_cases h : ∃ k, coordDeriv k u x ≠ 0
    · obtain ⟨k,hk⟩ := h
      exact (mul_pos (hVolume x hx') (covectorSq_pos (hg.2 x hx') hk)).le
    · push Not at h
      simp [W,covectorSq,h]
  have hInt : IntegrableOn W (ball (0 : (X dim)) 1) :=
    ((hW.mono hBU).integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hAE := (integral_eq_zero_iff_of_nonneg_ae hNon hInt).mp hZ
  have hWe : EqOn W 0 (ball (0 : (X dim)) 1) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) hAE isOpen_ball
      (hW.mono (ball_subset_closedBall.trans hBU)) continuousOn_const
  have hD (x : (X dim)) (hx : x ∈ ball (0 : (X dim)) 1) : fderiv ℝ u x = 0 := by
    apply ContinuousLinearMap.ext
    intro a
    have hAxis (i : (I dim)) : coordDeriv i u x = 0 := by
      by_contra h
      have hp := mul_pos (hVolume x (hBU (ball_subset_closedBall hx)))
        (covectorSq_pos (hg.2 x (hBU (ball_subset_closedBall hx))) h)
      exact (ne_of_gt hp) (hWe hx)
    conv_lhs => rw [← vector_eq_sum_axis a]
    simp only [map_sum,map_smul,show ∀ i, (fderiv ℝ u x) (axis i) = 0 from hAxis,
      smul_zero,Finset.sum_const_zero,zero_apply]
  have hEq : EqOn u (fun _ => u 0) (ball (0 : (X dim)) 1) :=
    isOpen_ball.eqOn_of_fderiv_eq (convex_ball _ _).isPreconnected
      ((hu.mono (ball_subset_closedBall.trans hBU)).differentiableOn (by simp))
      (differentiableOn_const _) (fun x hx => by rw [hD x hx]; simp)
      (mem_ball_self one_pos) rfl
  have hCB : closure (ball (0 : (X dim)) 1) = closedBall (0 : (X dim)) 1 := closure_ball _ one_ne_zero
  have hEq' : EqOn u (fun _ => u 0) (closedBall (0 : (X dim)) 1) := by
    apply hEq.of_subset_closure
    · exact hu.continuousOn.mono hBU
    · exact continuousOn_const
    · exact ball_subset_closedBall
    · rw [hCB]
  have hb : axis 0 ∈ (standardSphere dim) := by
    rw [standardSphere,mem_sphere,dist_zero_right,axis,PiLp.norm_single]
    norm_num
  have hz : u 0 = 0 := (hEq' (sphere_subset_closedBall hb)).symm.trans (hBdy hb)
  exact fun x hx => (hEq' hx).trans hz

end CalderonN
