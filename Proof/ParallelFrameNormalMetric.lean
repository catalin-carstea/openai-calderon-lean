import Proof.NormalMetricTensorFamily
import Proof.FramedNormalMetric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- A local affine frame curve with exactly the parallel first jet at the
    selected center. It need not be orthonormal away from that center. -/
def affineParallelFrame (g : MetricField) (y a : X) (L : X →L[ℝ] X) (t : ℝ) : X →L[ℝ] X :=
  L-t • (connectionBilinear g y a).comp L

def parallelFrameNormalMetric (g : MetricField) (E : X × X → X) (y a : X) (r : ℝ)
    (L : X →L[ℝ] X) (p : ℝ × X) : Mat :=
  fun i j => jointNormalMetricPair g E (affineParallelFrame g y a L p.1 (axis i))
    (affineParallelFrame g y a L p.1 (axis j)) (y+p.1 • a,r • affineParallelFrame g y a L p.1 p.2)

lemma affineParallelFrame_zero (g : MetricField) (y a : X) (L : X →L[ℝ] X) :
    affineParallelFrame g y a L 0 = L := by simp only [affineParallelFrame,zero_smul,sub_zero]

lemma hasDerivAt_affineParallelFrame (g : MetricField) (y a : X) (L : X →L[ℝ] X) (s : ℝ) :
    HasDerivAt (affineParallelFrame g y a L) (-((connectionBilinear g y a).comp L)) s := by
  have hb := (hasDerivAt_const s L).sub ((hasDerivAt_id s).smul_const ((connectionBilinear g y a).comp L))
  change HasDerivAt (affineParallelFrame g y a L) _ s at hb
  simpa only [one_smul,zero_sub] using hb

lemma hasDerivAt_affineParallelFrame_apply (g : MetricField) (y a : X) (L : X →L[ℝ] X) (s : ℝ) (z : X) :
    HasDerivAt (fun t => affineParallelFrame g y a L t z) (-connection g y a (L z)) s := by
  have hb := (hasDerivAt_affineParallelFrame g y a L s).clm_apply (hasDerivAt_const s z)
  simpa only [_root_.neg_apply,ContinuousLinearMap.comp_apply,connectionBilinear_apply,
    map_zero,add_zero] using hb

lemma parallelFrameNormalMetric_zero (g : MetricField) (E : X × X → X) (y a : X) (r : ℝ) (e : Frame) (z : X) :
    parallelFrameNormalMetric g E y a r (frameVectorLinear e y) (0,z) = framedNormalMetric g e E y r z := by
  ext i j
  simp only [parallelFrameNormalMetric,affineParallelFrame_zero,zero_smul,add_zero,
    frameVectorLinear_apply,frameVector_axis,jointNormalMetricPair,framedNormalMetric,normalPullbackMetricPair,
    normalVerticalJacobian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]

/-- The actual center derivative of this local metric family is exactly the
    previously bounded covariant tensor derivative, with the same witnesses. -/
theorem hasDerivAt_parallelFrameNormalMetric_center (g : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X) (i j : I)
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (y,r • L z)) :
    HasDerivAt (fun t => parallelFrameNormalMetric g E y a r L (t,z) i j)
      (normalMetricCovariantCenter g E y (r • L z) a (L (axis i)) (L (axis j))) 0 := by
  let p : ℝ → X × X := fun t => (y+t • a,r • affineParallelFrame g y a L t z)
  let U : ℝ → X := fun t => affineParallelFrame g y a L t (axis i)
  let W : ℝ → X := fun t => affineParallelFrame g y a L t (axis j)
  have hp : HasDerivAt p (a,-connection g y a (r • L z)) 0 := by
    have hCenter := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
    have hVelocity := (hasDerivAt_affineParallelFrame_apply g y a L 0 z).const_smul r
    convert hCenter.prodMk hVelocity using 1 <;>
      simp only [p,Pi.add_apply,Pi.smul_apply,Function.id_def,one_smul,zero_add,← connectionBilinear_apply,map_smul,smul_neg]
  have hU := hasDerivAt_affineParallelFrame_apply g y a L 0 (axis i)
  have hW := hasDerivAt_affineParallelFrame_apply g y a L 0 (axis j)
  have hp0 : p 0 = (y,r • L z) := by simp only [p,zero_smul,add_zero,affineParallelFrame_zero]
  have hT0 : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (p 0) := by rw [hp0];exact hT
  have hb := hasDerivAt_jointNormalMetricPair_curve g E p U W 0 (a,-connection g y a (r • L z))
    (-connection g y a (L (axis i))) (-connection g y a (L (axis j))) hT0 hp hU hW
  simp only [U,W,affineParallelFrame_zero,hp0] at hb
  change HasDerivAt (fun t => parallelFrameNormalMetric g E y a r L (t,z) i j) _ 0 at hb
  convert hb using 1
  simp only [normalMetricCovariantCenter,jointNormalMetricPair_neg_left,jointNormalMetricPair_neg_right]
  abel

end ShrinkingSpheres
