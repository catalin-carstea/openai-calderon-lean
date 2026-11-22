module

public import Proof.CalderonN.FixedBallWeakEnergyBound
public import Proof.CalderonN.WeakDirichletCorrection

import Mathlib.Tactic

/-! The dimension-general weak coefficient operator, with all norms
taken on the same native fixed-ball space as the strong Dirichlet operator. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open TauCeti PDE

variable {dim : ℕ} [NeZero dim]

omit [NeZero dim] in
private theorem memLp_fixedBall_smoothEnergy {a : X dim → Mat dim} (ha : Continuous a) :
    MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) := by
  let q (x : X dim) := energyIntegrand (a x) 0 0
  have hq : Continuous q := Continuous.energyIntegrand ha continuous_const continuous_const
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : X dim) 1).exists_bound_of_continuousOn hq.continuousOn
  refine memLp_top_of_bound hq.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with x hx
  exact hC _ (ball_subset_closedBall hx)

def fixedBallSmoothEnergyL {a : X dim → Mat dim} (ha : Continuous a) :
    FixedBallH1 dim →L[ℝ] FixedBallH1 dim →L[ℝ] ℝ :=
  energyFormH1L (memLp_fixedBall_smoothEnergy ha)

omit [NeZero dim] in
theorem fixedBallSmoothEnergyL_apply {a : X dim → Mat dim} (ha : Continuous a)
    (u v : FixedBallH1 dim) :
    fixedBallSmoothEnergyL ha u v = energyFormH1 a 0 0 u v := by
  unfold fixedBallSmoothEnergyL
  exact energyFormH1L_apply _ u v

theorem norm_fixedBallSmoothEnergyL_le {a : X dim → Mat dim} (ha : Continuous a)
    (q : ℝ) (hq : 0 ≤ q) (hEntry : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ∀ i j, |a x i j| ≤ q) :
    ‖fixedBallSmoothEnergyL ha‖ ≤ (dim : ℝ)^2*q := by
  unfold fixedBallSmoothEnergyL
  exact norm_fixedBall_weakEnergy_entrywise_le (memLp_fixedBall_smoothEnergy ha) q hq hEntry

omit [NeZero dim] in
theorem fixedBallSmoothEnergyL_add {a b : X dim → Mat dim} (ha : Continuous a) (hb : Continuous b) :
    fixedBallSmoothEnergyL (ha.add hb : Continuous (a+b)) =
      fixedBallSmoothEnergyL ha+fixedBallSmoothEnergyL hb := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply,fixedBallSmoothEnergyL_apply,energyFormH1_def]
  let μ := (volume : Measure (X dim)).restrict (fixedBallOpens dim)
  let A (x : X dim) := energyIntegrand (a x) 0 0 (jetField u x) (jetField v x)
  let B (x : X dim) := energyIntegrand (b x) 0 0 (jetField u x) (jetField v x)
  calc
    _ = ∫ x, A x + B x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      change energyIntegrand (a x+b x) 0 0 (jetField u x) (jetField v x) = _
      simpa only [add_zero] using
        energyIntegrand_add_apply (a x) (b x) 0 0 0 0 (jetField u x) (jetField v x)
    _ = _ := integral_add
      (integrable_energyIntegrand_jetField (memLp_fixedBall_smoothEnergy ha) u v)
      (integrable_energyIntegrand_jetField (memLp_fixedBall_smoothEnergy hb) u v)

omit [NeZero dim] in
theorem fixedBallSmoothEnergyL_smul {a : X dim → Mat dim} (ha : Continuous a) (c : ℝ) :
    fixedBallSmoothEnergyL (ha.const_smul c : Continuous (c • a)) = c • fixedBallSmoothEnergyL ha := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,fixedBallSmoothEnergyL_apply,energyFormH1_def,smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  change energyIntegrand (c • a x) 0 0 (jetField u x) (jetField v x) = _
  simpa only [smul_zero,mul_zero,Pi.zero_apply] using
    energyIntegrand_smul_apply (a x) 0 0 c (jetField u x) (jetField v x)

omit [NeZero dim] in
theorem fixedBallSmoothEnergyL_sub {a b : X dim → Mat dim} (ha : Continuous a) (hb : Continuous b) :
    fixedBallSmoothEnergyL (ha.sub hb : Continuous (a-b)) =
      fixedBallSmoothEnergyL ha-fixedBallSmoothEnergyL hb := by
  have h := fixedBallSmoothEnergyL_add (ha.sub hb) hb
  have hL : fixedBallSmoothEnergyL ((ha.sub hb).add hb : Continuous ((a-b)+b)) =
      fixedBallSmoothEnergyL ha := by
    ext u v
    simp only [fixedBallSmoothEnergyL_apply, sub_add_cancel]
  rw [hL] at h
  rw [h,add_sub_cancel_right]

open scoped InnerProductSpace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Native inclusion of the zero-Dirichlet ball space. -/
@[expose] def fixedBallZeroInclusionL (dim : ℕ) :
    FixedBallH1Zero dim →L[ℝ] FixedBallH1 dim :=
  (w1p0Submodule volume (fixedBallOpens dim) 2).toSubmodule.subtypeL

theorem norm_fixedBallZeroInclusionL_le (dim : ℕ) : ‖fixedBallZeroInclusionL dim‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  unfold fixedBallZeroInclusionL
  rw [one_mul]
  exact le_rfl

/-- The unit-ball Poincaré constant gives weak coercivity at a coefficient
with ellipticity lower bound `lo`. -/
theorem fixedBallSmoothEnergy_zero_coercive {a : X dim → Mat dim} (ha : Continuous a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (u : FixedBallH1Zero dim) :
    (lo/5) * ‖u‖ * ‖u‖ ≤
      fixedBallSmoothEnergyL ha (fixedBallZeroInclusionL dim u) (fixedBallZeroInclusionL dim u) := by
  rw [fixedBallSmoothEnergyL_apply]
  have hP : ‖W1p.value (u : FixedBallH1 dim)‖ ≤ 2 * ‖W1p.gradient (u : FixedBallH1 dim)‖ := by
    cases dim with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ k =>
      have h := W1p.norm_value_le_mul_norm_gradient_of_subset_ball
        (p := 2) (by norm_num) (c := (0 : X (k+1))) (R := 1) Set.Subset.rfl u.2
      simpa only [mul_one] using h
  have h := hEll.div_mul_norm_sq_le_energyFormH1_self_of_zero_drift
    (b := fun _ => (0 : X dim)) (c := fun _ => (0 : ℝ)) (gamma := 0)
    ha.aestronglyMeasurable aestronglyMeasurable_const (fun _ _ => rfl)
    (fun _ _ => by simp) (fun _ _ => le_rfl) hP
  change (lo/5)*‖(u : FixedBallH1 dim)‖*‖(u : FixedBallH1 dim)‖ ≤
    energyFormH1 a 0 0 (u : FixedBallH1 dim) (u : FixedBallH1 dim)
  convert h using 1
  ring

theorem isCoercive_fixedBallSmoothEnergy {a : X dim → Mat dim} (ha : Continuous a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi) :
    IsCoercive (zeroDirichletEnergy (fixedBallZeroInclusionL dim) (fixedBallSmoothEnergyL ha)) := by
  refine ⟨lo/5,by have := hEll.pos; positivity,fun u => ?_⟩
  rw [zeroDirichletEnergy_apply]
  exact fixedBallSmoothEnergy_zero_coercive ha hEll u

end CalderonN
