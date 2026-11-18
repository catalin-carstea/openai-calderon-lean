import Proof.JointNormalMetricSegmentJets
import Proof.MixedCenterTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The true reference pullback tensor has a quadratic center derivative
    remainder and a linearly vanishing mixed vertical-center derivative,
    uniformly in all fixed tangent witnesses. No chosen-frame jets enter. -/
theorem Background.reference_normal_metric_center_taylor {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v u w a b : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (jointNormalMetricPair g expMap u w) (y,v) (a,0)-metricDifferential g y a u w‖ ≤
      backgroundJointNormalMetricJetBudget hm K M*‖v‖^2*‖a‖*‖u‖*‖w‖ ∧
    ‖fderiv ℝ (fderiv ℝ (jointNormalMetricPair g expMap u w)) (y,v) (0,b) (a,0)‖ ≤
      backgroundJointNormalMetricJetBudget hm K M*‖v‖*‖b‖*‖a‖*‖u‖*‖w‖ := by
  let B := jointNormalMetricPair g expMap u w
  let C := backgroundJointNormalMetricJetBudget hm K M*‖u‖*‖w‖
  have hV := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hBudget : 0 ≤ backgroundJointNormalMetricJetBudget hm K M := by
    dsimp [backgroundJointNormalMetricJetBudget]
    positivity
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hSegment := h.joint_normal_metric_segment_jets hY hΩ hK hm hN hR hy v u w hv hv1 g (by simp)
  have hSmooth (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ B (y,t • v) := (hSegment t ht).1
  have hVertical (z : X) : (fun x : X => fderiv ℝ B (x,0) (0,z)) =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact h.joint_normal_metric_vertical_zero hΩ hK (by omega) hN hx u w z
  have hThird (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (y,t • v)‖ ≤ C := by
    have hb := (hSegment t ht).2 3 (by omega)
    change ‖iteratedFDeriv ℝ 3 B (y,t • v)‖ ≤ C at hb
    rwa [← norm_iteratedFDeriv_fderiv (n:=2),← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hb
  constructor
  · have hb := norm_center_fderiv_sub_zero_quadratic_of_third_bound B y a v hSmooth (hVertical v) C hC hThird
    rw [h.joint_normal_metric_center_zero hY hΩ hN hy u w a] at hb
    exact hb.trans_eq (by dsimp only [C];ring)
  · have hb := norm_center_velocity_second_fderiv_of_third_bound B y a v b hSmooth (hVertical b) C hC hThird
    exact hb.trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres
