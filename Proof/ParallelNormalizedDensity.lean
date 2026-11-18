import Proof.ParallelFrameMetricJets
import Proof.NormalizedDensityCovariantCenter

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalizedDensityAffineRemainder (g g₁ : MetricField) (E : X × X → X) (p : X × X) : ℝ :=
  normalizedJointFirstDensityFactor g g₁ E p-1-firstDensityLogDifferential g g₁ p.1 p.2

def parallelNormalizedDensity (g g₁ : MetricField) (E : X × X → X) (y a : X) (r : ℝ)
    (L : X →L[ℝ] X) (p : ℝ × X) : ℝ :=
  normalizedJointFirstDensityFactor g g₁ E (parallelFrameInput g y a r L p)

def parallelNormalizedDensityRemainder (g g₁ : MetricField) (E : X × X → X) (y a : X) (r : ℝ)
    (L : X →L[ℝ] X) (p : ℝ × X) : ℝ :=
  normalizedDensityAffineRemainder g g₁ E (parallelFrameInput g y a r L p)

lemma contDiffAt_normalizedDensityAffineRemainder (g g₁ : MetricField) (E : X × X → X) (y v : X)
    (hF : ContDiffAt ℝ ∞ (normalizedJointFirstDensityFactor g g₁ E) (y,v))
    (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) y) :
    ContDiffAt ℝ ∞ (normalizedDensityAffineRemainder g g₁ E) (y,v) := by
  exact (hF.sub contDiffAt_const).sub ((hEll.comp (y,v) contDiffAt_fst).clm_apply contDiffAt_snd)

lemma fderiv_normalizedDensityAffineRemainder_covariant (g g₁ : MetricField) (E : X × X → X) (y v a : X)
    (hF : ContDiffAt ℝ ∞ (normalizedJointFirstDensityFactor g g₁ E) (y,v))
    (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) y) :
    fderiv ℝ (normalizedDensityAffineRemainder g g₁ E) (y,v) (a,-connection g y a v) =
      normalizedDensityCovariantCenterRemainder g g₁ E y v a := by
  have hLinear := ((hEll.differentiableAt (by simp)).hasFDerivAt.comp (y,v)
    (hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,v)))).clm_apply (hasFDerivAt_snd (𝕜:=ℝ) (p:=(y,v)))
  have hAll := ((hF.differentiableAt (by simp)).hasFDerivAt.sub (hasFDerivAt_const (1:ℝ) (y,v))).sub hLinear
  have hh := congrArg (fun D : (X × X) →L[ℝ] ℝ => D (a,-connection g y a v)) hAll.fderiv
  change fderiv ℝ (normalizedDensityAffineRemainder g g₁ E) (y,v) (a,-connection g y a v) = _ at hh
  rw [hh]
  simp only [_root_.sub_apply,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,zero_apply]
  change fderiv ℝ (normalizedJointFirstDensityFactor g g₁ E) (y,v) (a,-connection g y a v)-0-
    (firstDensityLogDifferential g g₁ y (-connection g y a v)+fderiv ℝ (firstDensityLogDifferential g g₁) y a v) = _
  simp only [normalizedDensityCovariantCenterRemainder,firstDensityLogCovariantDerivative,
    _root_.sub_apply,ContinuousLinearMap.comp_apply,connectionBilinear_apply,map_neg]
  ring

lemma hasDerivAt_parallelFrameInput_center (g : MetricField) (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X) :
    HasDerivAt (fun t => parallelFrameInput g y a r L (t,z)) (a,-connection g y a (r • L z)) 0 := by
  have hCenter := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  have hVelocity := (hasDerivAt_affineParallelFrame_apply g y a L 0 z).const_smul r
  convert hCenter.prodMk hVelocity using 1 <;>
    simp only [parallelFrameInput,Pi.add_apply,Pi.smul_apply,Function.id_def,one_smul,zero_add,
      ← connectionBilinear_apply,map_smul,smul_neg]

lemma fderiv_parallelNormalizedDensityRemainder_center (g g₁ : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X)
    (hF : ContDiffAt ℝ ∞ (normalizedJointFirstDensityFactor g g₁ E) (y,r • L z))
    (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) y) :
    fderiv ℝ (parallelNormalizedDensityRemainder g g₁ E y a r L) (0,z) (1,0) =
      normalizedDensityCovariantCenterRemainder g g₁ E y (r • L z) a := by
  have hR := contDiffAt_normalizedDensityAffineRemainder g g₁ E y (r • L z) hF hEll
  have hInput : ContDiffAt ℝ ∞ (parallelFrameInput g y a r L) (0,z) := (contDiff_parallelFrameInput g y a r L).contDiffAt
  have hRInput : ContDiffAt ℝ ∞ (normalizedDensityAffineRemainder g g₁ E) (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hR
  have hSmooth := hRInput.comp (0,z) hInput
  have hTime := (hSmooth.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
    ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) z))
  have hOther := (hRInput.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_parallelFrameInput_center g y a r L z)
  have hEq := hTime.unique hOther
  change fderiv ℝ (parallelNormalizedDensityRemainder g g₁ E y a r L) (0,z) (1,0) = _ at hEq
  exact hEq.trans (by
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using
      fderiv_normalizedDensityAffineRemainder_covariant g g₁ E y (r • L z) a hF hEll)

/-- True mixed angular derivative of the same normalized scalar remainder. -/
theorem fderiv_parallelNormalizedDensityRemainder_mixed (g g₁ : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z b : X)
    (W : Set (X × X)) (hW : IsOpen W) (hp : (y,r • L z) ∈ W)
    (hF : ContDiffOn ℝ ∞ (normalizedJointFirstDensityFactor g g₁ E) W)
    (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) y) :
    fderiv ℝ (fderiv ℝ (parallelNormalizedDensityRemainder g g₁ E y a r L)) (0,z) (0,b) (1,0) =
      fderiv ℝ (fun v => normalizedDensityCovariantCenterRemainder g g₁ E y v a) (r • L z) (r • L b) := by
  have hF0 := hF.contDiffAt (hW.mem_nhds hp)
  have hR := contDiffAt_normalizedDensityAffineRemainder g g₁ E y (r • L z) hF0 hEll
  have hInput : ContDiffAt ℝ ∞ (parallelFrameInput g y a r L) (0,z) := (contDiff_parallelFrameInput g y a r L).contDiffAt
  have hRInput : ContDiffAt ℝ ∞ (normalizedDensityAffineRemainder g g₁ E) (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hR
  have hSmooth : ContDiffAt ℝ ∞ (parallelNormalizedDensityRemainder g g₁ E y a r L) (0,z) := hRInput.comp (0,z) hInput
  let C := fun w => normalizedDensityCovariantCenterRemainder g g₁ E y (r • L w) a
  have hContinuous : ContinuousAt (fun w : X => (y,r • L w)) z :=
    continuousAt_const.prodMk (L.continuous.continuousAt.const_smul r)
  have hNear : (fun w => fderiv ℝ (parallelNormalizedDensityRemainder g g₁ E y a r L) (0,w) (1,0)) =ᶠ[𝓝 z] C := by
    filter_upwards [hContinuous.eventually (hW.mem_nhds hp)] with w hw
    exact fderiv_parallelNormalizedDensityRemainder_center g g₁ E y a r L w (hF.contDiffAt (hW.mem_nhds hw)) hEll
  have hMixed := mixed_first_coordinate_fderiv_of_germ (parallelNormalizedDensityRemainder g g₁ E y a r L) z b C hSmooth hNear
  have hScale : HasFDerivAt (fun w => r • L w) (r • L) z := by convert (r • L).hasFDerivAt using 1
  have hIn : ContDiffAt ℝ ∞ (fun v : X => (y,v)) (r • L z) := contDiffAt_const.prodMk contDiffAt_id
  have hDir : ContDiffAt ℝ ∞ (fun v : X => (a,-connection g y a v)) (r • L z) := by
    convert (contDiffAt_const (c:=a)).prodMk ((connectionBilinear g y a).contDiff.contDiffAt.neg) using 1
    funext v;simp only [Pi.neg_apply,connectionBilinear_apply]
  have hCov : ContDiffAt ℝ ∞ (fun v => normalizedDensityCovariantCenterRemainder g g₁ E y v a) (r • L z) :=
    (((hF0.fderiv_right (m:=∞) (by simp)).comp _ hIn).clm_apply hDir).sub
      ((firstDensityLogCovariantDerivative g g₁ y a).contDiff.contDiffAt)
  have hComp := (hCov.differentiableAt (by simp)).hasFDerivAt.comp z hScale
  simp only [Function.comp_def] at hComp
  exact hMixed.trans (congrArg (fun T : X →L[ℝ] ℝ => T b) hComp.fderiv)

lemma fderiv_parallelNormalizedDensityRemainder_vertical (g g₁ : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z b : X)
    (hF : ContDiffAt ℝ ∞ (normalizedJointFirstDensityFactor g g₁ E) (y,r • L z))
    (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) y) :
    fderiv ℝ (parallelNormalizedDensityRemainder g g₁ E y a r L) (0,z) (0,b) =
      fderiv ℝ (normalizedJointFirstDensityFactor g g₁ E) (y,r • L z) (0,r • L b)-
        firstDensityLogDifferential g g₁ y (r • L b) := by
  have hR := contDiffAt_normalizedDensityAffineRemainder g g₁ E y (r • L z) hF hEll
  have hRInput : ContDiffAt ℝ ∞ (normalizedDensityAffineRemainder g g₁ E) (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero] using hR
  have hSmooth := hRInput.comp (0,z) (contDiff_parallelFrameInput g y a r L).contDiffAt
  have hSlice := (hSmooth.differentiableAt (by simp)).hasFDerivAt.comp z
    ((hasFDerivAt_const (0:ℝ) z).prodMk (hasFDerivAt_id z))
  have hScale : HasFDerivAt (fun w => r • L w) (r • L) z := by convert (r • L).hasFDerivAt using 1
  have hIn := (hasFDerivAt_const y z).prodMk hScale
  have hN := (hF.differentiableAt (by simp)).hasFDerivAt.comp z hIn
  have hLinear := (firstDensityLogDifferential g g₁ y).hasFDerivAt.comp z hScale
  have hOther := (hN.sub (hasFDerivAt_const (1:ℝ) z)).sub hLinear
  have hFun : (fun w => normalizedJointFirstDensityFactor g g₁ E (y,r • L w)-1-
      firstDensityLogDifferential g g₁ y (r • L w)) =
      fun w => parallelNormalizedDensityRemainder g g₁ E y a r L (0,w) := by
    funext w;simp only [parallelNormalizedDensityRemainder,normalizedDensityAffineRemainder,
      parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero]
  change HasFDerivAt (fun w => normalizedJointFirstDensityFactor g g₁ E (y,r • L w)-1-
    firstDensityLogDifferential g g₁ y (r • L w)) _ z at hOther
  rw [hFun] at hOther
  have hEq := congrArg (fun D : X →L[ℝ] ℝ => D b) (hSlice.unique hOther)
  change fderiv ℝ (fun x : ℝ × X => normalizedDensityAffineRemainder g g₁ E (parallelFrameInput g y a r L x)) (0,z) (0,b) = _
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.inr_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
    _root_.sub_apply,zero_apply,sub_zero] using hEq

end ShrinkingSpheres
