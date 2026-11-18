import Proof.NormalMetricCovariantCenterDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The actual normal pullback as a bilinear tensor with both tangent slots
    retained. This is useful when a local frame moves with the center. -/
def normalJointMetricTensor (g : MetricField) (E : X × X → X) (p : X × X) : X →L[ℝ] X →L[ℝ] ℝ :=
  let J := normalVerticalJacobian E p.1 p.2
  ((ContinuousLinearMap.compL ℝ X X ℝ).flip J).comp ((metricBilinear g (E p)).comp J)

lemma normalJointMetricTensor_apply (g : MetricField) (E : X × X → X) (p : X × X) (u w : X) :
    normalJointMetricTensor g E p u w = jointNormalMetricPair g E u w p := by
  simp only [normalJointMetricTensor,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply,metricBilinear_apply,jointNormalMetricPair]

lemma jointNormalMetricPair_neg_left (g : MetricField) (E : X × X → X) (u w : X) (p : X × X) :
    jointNormalMetricPair g E (-u) w p = -jointNormalMetricPair g E u w p := by
  rw [← normalJointMetricTensor_apply,map_neg,_root_.neg_apply,normalJointMetricTensor_apply]

lemma jointNormalMetricPair_neg_right (g : MetricField) (E : X × X → X) (u w : X) (p : X × X) :
    jointNormalMetricPair g E u (-w) p = -jointNormalMetricPair g E u w p := by
  rw [← normalJointMetricTensor_apply,map_neg,normalJointMetricTensor_apply]

lemma contDiffAt_normalJointMetricTensor (g : MetricField) (E : X × X → X) (p : X × X)
    (hE : ContDiffAt ℝ ∞ E p) (hg : ∀ i j,ContDiffAt ℝ ∞ (fun x => g x i j) (E p)) :
    ContDiffAt ℝ ∞ (normalJointMetricTensor g E) p := by
  let J := fun q : X × X => normalVerticalJacobian E q.1 q.2
  have hJ : ContDiffAt ℝ ∞ J p :=
    (hE.fderiv_right (m:=∞) (by simp)).clm_comp contDiffAt_const
  have hL : ContDiffAt ℝ ∞ (fun q : X × X => metricBilinear g (E q)) p :=
    ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      ((hg i j).comp p hE).smul contDiffAt_const))
  have hR : ContDiffAt ℝ ∞ (fun q => (ContinuousLinearMap.compL ℝ X X ℝ).flip (J q)) p :=
    (ContinuousLinearMap.compL ℝ X X ℝ).flip.contDiff.contDiffAt.comp p hJ
  exact hR.clm_comp (hL.clm_comp hJ)

lemma fderiv_jointNormalMetricPair_eq_tensor (g : MetricField) (E : X × X → X)
    (p a : X × X) (u w : X) (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) p) :
    fderiv ℝ (jointNormalMetricPair g E u w) p a = fderiv ℝ (normalJointMetricTensor g E) p a u w := by
  have hEval := ((hT.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const u p)).clm_apply
    (hasFDerivAt_const w p)
  have hValue := congrArg (fun L : (X × X) →L[ℝ] ℝ => L a) hEval.fderiv
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    zero_apply,map_zero,zero_add] at hValue
  have hFun : (fun q => normalJointMetricTensor g E q u w) = jointNormalMetricPair g E u w := by
    funext q
    exact normalJointMetricTensor_apply g E q u w
  rwa [hFun] at hValue

/-- Moving tangent slots differentiate through the same actual tensor. -/
lemma hasDerivAt_jointNormalMetricPair_curve (g : MetricField) (E : X × X → X)
    (p : ℝ → X × X) (U W : ℝ → X) (s : ℝ) (dp : X × X) (du dw : X)
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (p s))
    (hp : HasDerivAt p dp s) (hU : HasDerivAt U du s) (hW : HasDerivAt W dw s) :
    HasDerivAt (fun t => jointNormalMetricPair g E (U t) (W t) (p t))
      (fderiv ℝ (jointNormalMetricPair g E (U s) (W s)) (p s) dp+
        jointNormalMetricPair g E du (W s) (p s)+jointNormalMetricPair g E (U s) dw (p s)) s := by
  have hL := (hT.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hp
  have hAll := (hL.clm_apply hU).clm_apply hW
  simp only [Function.comp_def,_root_.add_apply] at hAll
  have hFun : (fun t => normalJointMetricTensor g E (p t) (U t) (W t)) =
      (fun t => jointNormalMetricPair g E (U t) (W t) (p t)) := by
    funext t
    exact normalJointMetricTensor_apply g E (p t) (U t) (W t)
  rw [hFun] at hAll
  convert hAll using 1
  rw [fderiv_jointNormalMetricPair_eq_tensor g E (p s) dp (U s) (W s) hT,
    ← normalJointMetricTensor_apply g E (p s) du (W s),← normalJointMetricTensor_apply g E (p s) (U s) dw]

end ShrinkingSpheres
