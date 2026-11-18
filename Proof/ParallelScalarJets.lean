import Proof.ParallelFrameMetricJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma fderiv_comp_parallelFrameInput_center (F : X × X → ℝ) (g : MetricField)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X)
    (hF : ContDiffAt ℝ ∞ F (y,r • L z)) :
    fderiv ℝ (F ∘ parallelFrameInput g y a r L) (0,z) (1,0) =
      fderiv ℝ F (y,r • L z) (a,-connection g y a (r • L z)) := by
  have hAt : ContDiffAt ℝ ∞ F (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hF
  have hSmooth := hAt.comp (0,z) (contDiff_parallelFrameInput g y a r L).contDiffAt
  have hTime := (hSmooth.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
    ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) z))
  have hp : HasDerivAt (fun t => parallelFrameInput g y a r L (t,z))
      (a,-connection g y a (r • L z)) 0 := by
    have hCenter := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
    have hVelocity := (hasDerivAt_affineParallelFrame_apply g y a L 0 z).const_smul r
    convert hCenter.prodMk hVelocity using 1 <;>
      simp only [parallelFrameInput,Pi.add_apply,Pi.smul_apply,Function.id_def,one_smul,zero_add,
        ← connectionBilinear_apply,map_smul,smul_neg]
  have hOther := (hAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hp
  simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hTime.unique hOther

lemma fderiv_comp_parallelFrameInput_vertical (F : X × X → ℝ) (g : MetricField)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z b : X)
    (hF : ContDiffAt ℝ ∞ F (y,r • L z)) :
    fderiv ℝ (F ∘ parallelFrameInput g y a r L) (0,z) (0,b) =
      fderiv ℝ F (y,r • L z) (0,r • L b) := by
  have hAt : ContDiffAt ℝ ∞ F (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hF
  have hSmooth := hAt.comp (0,z) (contDiff_parallelFrameInput g y a r L).contDiffAt
  have hSlice := (hSmooth.differentiableAt (by simp)).hasFDerivAt.comp z
    ((hasFDerivAt_const (0:ℝ) z).prodMk (hasFDerivAt_id z))
  have hScale : HasFDerivAt (fun w => r • L w) (r • L) z := by convert (r • L).hasFDerivAt using 1
  have hOther := (hF.differentiableAt (by simp)).hasFDerivAt.comp z ((hasFDerivAt_const y z).prodMk hScale)
  have hFun : (fun w => (F ∘ parallelFrameInput g y a r L) (0,w)) = fun w => F (y,r • L w) := by
    funext w;simp only [Function.comp_def,parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero]
  simp only [Function.comp_def] at hSlice hOther
  have hEq := hSlice.fderiv
  change fderiv ℝ (fun w => (F ∘ parallelFrameInput g y a r L) (0,w)) z = _ at hEq
  rw [hFun,hOther.fderiv] at hEq
  have hh := congrArg (fun D : X →L[ℝ] ℝ => D b) hEq
  change fderiv ℝ (fun x : ℝ × X => F (parallelFrameInput g y a r L x)) (0,z) (0,b) = _
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.id_apply,zero_apply,_root_.smul_apply] using hh.symm

/-- Mixed chain rule with only the center/angular jet, without a pure center
    second derivative of the nonorthonormal local affine frame. -/
theorem fderiv_comp_parallelFrameInput_mixed (F : X × X → ℝ) (g : MetricField)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z b : X)
    (W : Set (X × X)) (hW : IsOpen W) (hp : (y,r • L z) ∈ W) (hF : ContDiffOn ℝ ∞ F W) :
    fderiv ℝ (fderiv ℝ (F ∘ parallelFrameInput g y a r L)) (0,z) (0,b) (1,0) =
      fderiv ℝ (fderiv ℝ F) (y,r • L z) (0,r • L b) (a,-connection g y a (r • L z))+
      fderiv ℝ F (y,r • L z) (0,-connection g y a (r • L b)) := by
  have hF0 := hF.contDiffAt (hW.mem_nhds hp)
  have hAt : ContDiffAt ℝ ∞ F (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hF0
  have hSmooth := hAt.comp (0,z) (contDiff_parallelFrameInput g y a r L).contDiffAt
  let C := fun w => fderiv ℝ F (y,r • L w) (a,-connection g y a (r • L w))
  have hContinuous : ContinuousAt (fun w : X => (y,r • L w)) z :=
    continuousAt_const.prodMk (L.continuous.continuousAt.const_smul r)
  have hNear : (fun w => fderiv ℝ (F ∘ parallelFrameInput g y a r L) (0,w) (1,0)) =ᶠ[𝓝 z] C := by
    filter_upwards [hContinuous.eventually (hW.mem_nhds hp)] with w hw
    exact fderiv_comp_parallelFrameInput_center F g y a r L w (hF.contDiffAt (hW.mem_nhds hw))
  have hMixed := mixed_first_coordinate_fderiv_of_germ (F ∘ parallelFrameInput g y a r L) z b C hSmooth hNear
  have hScale : HasFDerivAt (fun w => r • L w) (r • L) z := by convert (r • L).hasFDerivAt using 1
  have hInput := (hasFDerivAt_const y z).prodMk hScale
  have hDF := ((hF0.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp z hInput
  have hDir := (hasFDerivAt_const a z).prodMk (((connectionBilinear g y a).hasFDerivAt.comp z hScale).neg)
  have hAll := hDF.clm_apply hDir
  simp only [Function.comp_def,Pi.neg_apply,connectionBilinear_apply] at hAll
  have hh := congrArg (fun D : X →L[ℝ] ℝ => D b) hAll.fderiv
  change fderiv ℝ C z b = _ at hh
  rw [hMixed,hh]
  simp only [Function.comp_def,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,zero_apply,_root_.neg_apply,_root_.smul_apply,connectionBilinear_apply]
  ring

end ShrinkingSpheres
