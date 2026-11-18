import Proof.ParallelFrameMetricRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma contDiffAt_jointNormalMetricPair_of_tensor (g : MetricField) (E : X × X → X)
    (p : X × X) (u w : X) (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) p) :
    ContDiffAt ℝ ∞ (jointNormalMetricPair g E u w) p := by
  have hb := (hT.clm_apply (contDiffAt_const (c:=u))).clm_apply (contDiffAt_const (c:=w))
  have hFun : (fun q => normalJointMetricTensor g E q u w) = jointNormalMetricPair g E u w := by
    funext q
    exact normalJointMetricTensor_apply g E q u w
  rwa [hFun] at hb

lemma contDiffAt_normalMetricCovariantCenter_of_tensor (g : MetricField) (E : X × X → X)
    (y v a u w : X) (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (y,v)) :
    ContDiffAt ℝ ∞ (fun z => normalMetricCovariantCenter g E y z a u w) v := by
  have hInput : ContDiffAt ℝ ∞ (fun z : X => (y,z)) v := contDiffAt_const.prodMk contDiffAt_id
  have hB := contDiffAt_jointNormalMetricPair_of_tensor g E (y,v) u w hT
  have hL := contDiffAt_jointNormalMetricPair_of_tensor g E (y,v) (connection g y a u) w hT
  have hR := contDiffAt_jointNormalMetricPair_of_tensor g E (y,v) u (connection g y a w) hT
  have hDir : ContDiffAt ℝ ∞ (fun z : X => (a,-connection g y a z)) v := by
    convert (contDiffAt_const (c:=a)).prodMk ((connectionBilinear g y a).contDiff.contDiffAt.neg) using 1
    funext z
    simp only [Pi.neg_apply,connectionBilinear_apply]
  exact ((((hB.fderiv_right (m:=∞) (by simp)).comp v hInput).clm_apply hDir).sub
    (hL.comp v hInput)).sub (hR.comp v hInput)

lemma contDiffAt_parallelFrameNormalMetric_entry (g : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X) (i j : I)
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (y,r • L z)) :
    ContDiffAt ℝ ∞ (fun p => parallelFrameNormalMetric g E y a r L p i j) (0,z) := by
  have hInput : ContDiffAt ℝ ∞ (parallelFrameInput g y a r L) (0,z) := (contDiff_parallelFrameInput g y a r L).contDiffAt
  have hTInput : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hT
  have hOp := hTInput.comp (0,z) hInput
  have hF : ContDiffAt ℝ ∞ (fun p : ℝ × X => affineParallelFrame g y a L p.1) (0,z) :=
    ((contDiff_affineParallelFrame g y a L).comp contDiff_fst).contDiffAt
  have hSlots := (hOp.clm_apply (hF.clm_apply (contDiffAt_const (c:=axis i)))).clm_apply
    (hF.clm_apply (contDiffAt_const (c:=axis j)))
  simpa only [Function.comp_def,normalJointMetricTensor_apply,parallelFrameInput,parallelFrameNormalMetric] using hSlots

lemma fderiv_parallelFrameNormalMetric_center (g : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X) (i j : I)
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (y,r • L z)) :
    fderiv ℝ (fun p => parallelFrameNormalMetric g E y a r L p i j) (0,z) (1,0) =
      normalMetricCovariantCenter g E y (r • L z) a (L (axis i)) (L (axis j)) := by
  have hG := contDiffAt_parallelFrameNormalMetric_entry g E y a r L z i j hT
  have hInput : HasDerivAt (fun t : ℝ => (t,z)) ((1:ℝ),(0:X)) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 z)
  have hTime := (hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hInput
  exact hTime.unique (hasDerivAt_parallelFrameNormalMetric_center g E y a r L z i j hT)

lemma fderiv_parallelFrameNormalMetric_vertical (g : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z b : X) (i j : I)
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (y,r • L z)) :
    fderiv ℝ (fun p => parallelFrameNormalMetric g E y a r L p i j) (0,z) (0,b) =
      fderiv ℝ (jointNormalMetricPair g E (L (axis i)) (L (axis j))) (y,r • L z) (0,r • L b) := by
  have hG := contDiffAt_parallelFrameNormalMetric_entry g E y a r L z i j hT
  have hB := contDiffAt_jointNormalMetricPair_of_tensor g E (y,r • L z) (L (axis i)) (L (axis j)) hT
  have hInput : HasFDerivAt (fun w : X => ((0:ℝ),w)) (ContinuousLinearMap.inr ℝ ℝ X) z :=
    (hasFDerivAt_const (0:ℝ) z).prodMk (hasFDerivAt_id z)
  have hScale : HasFDerivAt (fun w => r • L w) (r • L) z := by convert (r • L).hasFDerivAt using 1
  have hBInput := (hasFDerivAt_const y z).prodMk hScale
  have hSlice := (hG.differentiableAt (by simp)).hasFDerivAt.comp z hInput
  have hBSlice := (hB.differentiableAt (by simp)).hasFDerivAt.comp z hBInput
  simp only [Function.comp_def] at hSlice hBSlice
  have hFun : (fun w => parallelFrameNormalMetric g E y a r L (0,w) i j) =
      (fun w => jointNormalMetricPair g E (L (axis i)) (L (axis j)) (y,r • L w)) := by
    funext w
    simp only [parallelFrameNormalMetric,affineParallelFrame_zero,zero_smul,add_zero]
  have hEq := hSlice.fderiv
  rw [hFun,hBSlice.fderiv] at hEq
  have hValue := congrArg (fun D : X →L[ℝ] ℝ => D b) hEq
  exact hValue.symm

lemma mixed_first_coordinate_fderiv_of_germ (F : ℝ × X → ℝ) (z b : X) (C : X → ℝ)
    (hF : ContDiffAt ℝ ∞ F (0,z))
    (hNear : (fun w => fderiv ℝ F (0,w) (1,0)) =ᶠ[𝓝 z] C) :
    fderiv ℝ (fderiv ℝ F) (0,z) (0,b) (1,0) = fderiv ℝ C z b := by
  have hInput : HasFDerivAt (fun w : X => ((0:ℝ),w)) (ContinuousLinearMap.inr ℝ ℝ X) z :=
    (hasFDerivAt_const (0:ℝ) z).prodMk (hasFDerivAt_id z)
  have hDF := ((hF.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp z hInput
  have hEval := hDF.clm_apply (hasFDerivAt_const ((1:ℝ),(0:X)) z)
  simp only [Function.comp_def] at hEval
  have hValue := congrArg (fun L : X →L[ℝ] ℝ => L b) (hEval.fderiv.symm.trans hNear.fderiv_eq)
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inr_apply,zero_apply,map_zero,zero_add] using hValue

/-- Differentiating the exact center identity gives the actual mixed angular
    jet of the SAME local parallel-frame family. -/
theorem fderiv_parallelFrameNormalMetric_mixed (g : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z b : X) (i j : I)
    (W : Set (X × X)) (hW : IsOpen W) (hp : (y,r • L z) ∈ W)
    (hT : ContDiffOn ℝ ∞ (normalJointMetricTensor g E) W) :
    fderiv ℝ (fderiv ℝ (fun p => parallelFrameNormalMetric g E y a r L p i j)) (0,z) (0,b) (1,0) =
      fderiv ℝ (fun v => normalMetricCovariantCenter g E y v a (L (axis i)) (L (axis j))) (r • L z) (r • L b) := by
  have hT0 := hT.contDiffAt (hW.mem_nhds hp)
  have hG := contDiffAt_parallelFrameNormalMetric_entry g E y a r L z i j hT0
  let C := fun w => normalMetricCovariantCenter g E y (r • L w) a (L (axis i)) (L (axis j))
  have hContinuous : ContinuousAt (fun w : X => (y,r • L w)) z :=
    continuousAt_const.prodMk (L.continuous.continuousAt.const_smul r)
  have hNear : (fun w => fderiv ℝ (fun p => parallelFrameNormalMetric g E y a r L p i j) (0,w) (1,0)) =ᶠ[𝓝 z] C := by
    filter_upwards [hContinuous.eventually (hW.mem_nhds hp)] with w hw
    exact fderiv_parallelFrameNormalMetric_center g E y a r L w i j (hT.contDiffAt (hW.mem_nhds hw))
  have hMixed := mixed_first_coordinate_fderiv_of_germ (fun p => parallelFrameNormalMetric g E y a r L p i j) z b C hG hNear
  have hCov := contDiffAt_normalMetricCovariantCenter_of_tensor g E y (r • L z) a (L (axis i)) (L (axis j)) hT0
  have hScale : HasFDerivAt (fun w => r • L w) (r • L) z := by
    convert (r • L).hasFDerivAt using 1
  have hComp := (hCov.differentiableAt (by simp)).hasFDerivAt.comp z hScale
  simp only [Function.comp_def] at hComp
  have hValue := congrArg (fun T : X →L[ℝ] ℝ => T b) hComp.fderiv
  exact hMixed.trans hValue

end ShrinkingSpheres
