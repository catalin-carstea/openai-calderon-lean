module

public import Proof.CalderonN.FixedBallSmoothFlux
public import Proof.CalderonN.ClassicalBallDirichlet

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! Uniqueness on the fixed ball for smooth representatives of the same
normalized divergence coefficient and trace. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Gradient Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 1250000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [Nontrivial (Fin dim)] in
private theorem eqOn_closedBall_zero_of_fderiv_eq_zero (u : SmoothData dim)
    (hD : EqOn (fderiv ℝ u.1) 0 (ball (0 : X dim) 1))
    (hT : EqOn u.1 0 (standardSphere dim)) : EqOn u.1 0 (closedBall (0 : X dim) 1) := by
  have hEq : EqOn u.1 (fun _ => u.1 0) (ball (0 : X dim) 1) :=
    isOpen_ball.eqOn_of_fderiv_eq (convex_ball _ _).isPreconnected
      (u.2.differentiable (by simp)).differentiableOn
      (differentiableOn_const _) (fun x hx => by rw [hD hx]; simp)
      (mem_ball_self one_pos) rfl
  have hEq' : EqOn u.1 (fun _ => u.1 0) (closedBall (0 : X dim) 1) := by
    apply hEq.of_subset_closure u.2.continuous.continuousOn continuousOn_const ball_subset_closedBall
    rw [closure_ball _ one_ne_zero]
  have hb : axis (0 : Fin dim) ∈ standardSphere dim := by
    rw [standardSphere,mem_sphere,dist_zero_right,axis,PiLp.norm_single]
    norm_num
  have hz : u.1 0 = 0 := (hEq' (sphere_subset_closedBall hb)).symm.trans (hT hb)
  exact fun x hx => (hEq' hx).trans hz

/-- The full smooth flux Green identity forces the gradient of a
homogeneous zero-trace solution to vanish. -/
theorem eqOn_closedUnitBall_of_negativeBallDivergence_eq_zero
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (u : SmoothData dim)
    (hEq : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1))
    (hT : EqOn u.1 0 (standardSphere dim)) : EqOn u.1 0 (closedBall (0 : X dim) 1) := by
  have hE := energyFormH1_smooth_eq_boundary_flux ha u u hEq
  have hZero : energyFormH1 a 0 0 (smoothSobolev u) (smoothSobolev u) = 0 := by
    rw [hE]
    have hI : (∫ w : ↥(standardSphere dim), u.1 w *
        inner ℝ (w : X dim) (smoothBallFlux a u.1 w) ∂(sphereProbability dim)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with w
      rw [show u.1 w = 0 from hT w.property,zero_mul,Pi.zero_apply]
    rw [hI,mul_zero]
  have hL := hEll.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift
    (b := fun _ => (0 : X dim)) (c := fun _ => (0 : ℝ)) (gamma := 0)
    ha.continuous.aestronglyMeasurable aestronglyMeasurable_const (fun _ _ => rfl)
    (fun _ _ => by simp) (fun _ _ => le_rfl) (smoothSobolev u)
  have hGrad : TauCeti.W1p.gradient (smoothSobolev u) = 0 := by
    change lo * ‖W1p.gradient (smoothSobolev u)‖ ^ 2 ≤ energyFormH1 a 0 0 (smoothSobolev u) (smoothSobolev u) at hL
    rw [hZero] at hL
    by_contra h
    exact (not_lt_of_ge hL) (mul_pos hEll.pos (sq_pos_of_pos (norm_pos_iff.mpr h)))
  have hAE := gradient_smoothSobolev_ae u
  rw [hGrad] at hAE
  have hG : EqOn (gradient u.1) 0 (ball (0 : X dim) 1) := by
    have h' : gradient u.1 =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] 0 :=
      hAE.symm.trans (Lp.coeFn_zero _ _ _)
    exact Measure.eqOn_open_of_ae_eq h' isOpen_ball
      (u.2.gradient_right (m := 0) (by simp)).continuous.continuousOn continuousOn_const
  have hD : EqOn (fderiv ℝ u.1) 0 (ball (0 : X dim) 1) := by
    intro x hx
    have hh : gradient u.1 x = 0 := hG hx
    rw [gradient] at hh
    exact (InnerProductSpace.toDual ℝ (X dim)).symm.injective (hh.trans (map_zero _).symm)
  exact eqOn_closedBall_zero_of_fderiv_eq_zero u hD hT

omit [NeZero dim] [Nontrivial (Fin dim)] in
/-- A change of smooth representative off the unit sphere cannot change
its outward derivative once the representatives agree on the closed ball. -/
theorem eqOn_radialDerivative_of_eqOn_closedUnitBall {u v : SmoothData dim}
    (h : EqOn u.1 v.1 (closedBall (0 : X dim) 1)) :
    EqOn (fun z => fderiv ℝ u.1 z z) (fun z => fderiv ℝ v.1 z z) (standardSphere dim) := by
  intro z hz
  have hzB : z ∈ closedBall (0 : X dim) 1 := sphere_subset_closedBall hz
  have hUnique : UniqueDiffWithinAt ℝ (closedBall (0 : X dim) 1) z :=
    (uniqueDiffOn_convex (convex_closedBall _ _) (by
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0,mem_ball_self one_pos⟩)) z hzB
  have he : fderiv ℝ u.1 z = fderiv ℝ v.1 z := by
    rw [← ((u.2.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt).fderivWithin hUnique,
      ← ((v.2.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt).fderivWithin hUnique]
    exact fderivWithin_congr h (h hzB)
  exact congrArg (fun L : X dim →L[ℝ] ℝ => L z) he

theorem eqOn_closedUnitBall_of_equal_ball_forcing
    {a A : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (hA : EqOn a A (ball (0 : X dim) 1)) (u v : SmoothData dim)
    (hEq : EqOn (negativeBallDivergence A u.1) (negativeBallDivergence A v.1)
      (ball (0 : X dim) 1))
    (hT : EqOn u.1 v.1 (standardSphere dim)) : EqOn u.1 v.1 (closedBall (0 : X dim) 1) := by
  let d : SmoothData dim := ⟨fun z => u.1 z-v.1 z,u.2.sub v.2⟩
  have hD : EqOn (negativeBallDivergence a d.1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    have hg : a =ᶠ[𝓝 z] A := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hA hw
    have hSub := negativeBallDivergence_add ha u.2 v.2.neg z
    change negativeBallDivergence a (fun x => u.1 x+ -v.1 x) z =
      negativeBallDivergence a u.1 z+negativeBallDivergence a (fun x => -v.1 x) z at hSub
    have hNeg : negativeBallDivergence a (fun x => -v.1 x) z = -negativeBallDivergence a v.1 z := by
      unfold negativeBallDivergence Elliptic.Lop
      simp only [coordDeriv,fderiv_fun_neg,neg_apply,mul_neg,Finset.sum_neg_distrib,neg_neg]
    change negativeBallDivergence a (fun x => u.1 x-v.1 x) z = 0
    rw [show (fun x => u.1 x-v.1 x) = fun x => u.1 x+ -v.1 x from funext fun _ => sub_eq_add_neg _ _,
      hSub,hNeg,negativeBallDivergence_congr_germ hg EventuallyEq.rfl,
      negativeBallDivergence_congr_germ hg EventuallyEq.rfl,show
        negativeBallDivergence A u.1 z = negativeBallDivergence A v.1 z from hEq hz]
    ring
  intro z hz
  exact sub_eq_zero.mp (eqOn_closedUnitBall_of_negativeBallDivergence_eq_zero ha hEll d hD
    (fun x hx => sub_eq_zero.mpr (hT hx)) hz)

theorem eqOn_radialDerivative_of_classicalNormalResponses
    {a A : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (hA : EqOn a A (ball (0 : X dim) 1)) (u v : SmoothData dim)
    (hu : EqOn (negativeBallDivergence A u.1) 0 (ball (0 : X dim) 1))
    (hv : EqOn (negativeBallDivergence A v.1) 0 (ball (0 : X dim) 1))
    (hT : EqOn u.1 v.1 (standardSphere dim)) :
    EqOn (fun z => fderiv ℝ u.1 z z) (fun z => fderiv ℝ v.1 z z) (standardSphere dim) :=
  eqOn_radialDerivative_of_eqOn_closedUnitBall
    (eqOn_closedUnitBall_of_equal_ball_forcing ha hEll hA u v
      (fun z hz => (hu hz).trans (hv hz).symm) hT)

theorem smoothSobolev_eq_of_eqOn_ball (u v : SmoothData dim)
    (h : EqOn u.1 v.1 (ball (0 : X dim) 1)) : smoothSobolev u = smoothSobolev v := by
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  filter_upwards [value_smoothSobolev_ae u,value_smoothSobolev_ae v,
    ae_restrict_mem (μ := (volume : Measure (X dim))) (fixedBallOpens dim).isOpen.measurableSet]
    with z hu hv hz
  exact hu.trans ((h hz).trans hv.symm)

end CalderonN
