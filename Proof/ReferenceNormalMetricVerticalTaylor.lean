import Proof.JointNormalMetricSegmentJets
import Proof.VerticalZeroJetTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Shared actual tensor jets yield the quadratic value and linear vertical
    remainder without a separate Jacobian-smallness premise. -/
theorem Background.reference_normal_metric_vertical_taylor {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v u w : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖jointNormalMetricPair g expMap u w (y,v)-metricPair g y u w‖ ≤
      backgroundJointNormalMetricJetBudget hm K M*‖v‖^2*‖u‖*‖w‖ ∧
    ∀ b : X,‖fderiv ℝ (jointNormalMetricPair g expMap u w) (y,v) (0,b)‖ ≤
      backgroundJointNormalMetricJetBudget hm K M*‖v‖*‖b‖*‖u‖*‖w‖ := by
  let B := jointNormalMetricPair g expMap u w
  let C := backgroundJointNormalMetricJetBudget hm K M*‖u‖*‖w‖
  have hV := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hBudget : 0 ≤ backgroundJointNormalMetricJetBudget hm K M := by
    dsimp [backgroundJointNormalMetricJetBudget];positivity
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hSegment := h.joint_normal_metric_segment_jets hY hΩ hK hm hN hR hy v u w hv hv1 g (by simp)
  have hSecond (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖fderiv ℝ (fderiv ℝ B) (y,t • v)‖ ≤ C := by
    have hb := (hSegment t ht).2 2 (by omega)
    change ‖iteratedFDeriv ℝ 2 B (y,t • v)‖ ≤ C at hb
    rwa [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hb
  have hb := vertical_zero_jet_taylor B y v (fun t ht => (hSegment t ht).1)
    (fun b => h.joint_normal_metric_vertical_zero hΩ hK (by omega) hN hy u w b) C hC hSecond
  dsimp only [B] at hb
  rw [hN.joint_normal_metric_zero hy e (h.2.2.2.2.2.2.2 y (hN.center_mem hy)) u w] at hb
  exact ⟨hb.1.trans_eq (by dsimp only [C];ring),fun b => (hb.2 b).trans_eq (by dsimp only [C];ring)⟩

end ShrinkingSpheres
