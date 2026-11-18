import Proof.FrameCurveFirstJet
import Proof.CoordinateRotationOperatorDerivative
import Proof.ParallelFrameNormalMetric
import Proof.MovingRadius

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation

abbrev NormalFrameParameter := X × (ℝ × (X →L[ℝ] X))

def normalFrameActualCurve (e : Frame) (r : X → ℝ) (y a : X) (t : ℝ) : NormalFrameParameter :=
  (y+t • a,(r (y+t • a),frameVectorLinear e (y+t • a)))
def normalFrameParallelCurve (g : MetricField) (e : Frame) (r : X → ℝ) (y a : X) (t : ℝ) : NormalFrameParameter :=
  (y+t • a,(r y,affineParallelFrame g y a (frameVectorLinear e y) t))
def normalFrameRadiusCurve (e : Frame) (r : X → ℝ) (y : X) (t : ℝ) : NormalFrameParameter :=
  (y,((1+t)*r y,frameVectorLinear e y))
def normalFrameRotationCurve (e : Frame) (r : X → ℝ) (y : X) (i j : I) (t : ℝ) : NormalFrameParameter :=
  (y,(r y,(frameVectorLinear e y).comp
    (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap))

lemma normalFrameActualCurve_zero (e : Frame) (r : X → ℝ) (y a : X) :
    normalFrameActualCurve e r y a 0 = (y,(r y,frameVectorLinear e y)) := by simp [normalFrameActualCurve]
lemma normalFrameParallelCurve_zero (g : MetricField) (e : Frame) (r : X → ℝ) (y a : X) :
    normalFrameParallelCurve g e r y a 0 = (y,(r y,frameVectorLinear e y)) := by
  simp only [normalFrameParallelCurve,zero_smul,add_zero,affineParallelFrame_zero]
lemma normalFrameRadiusCurve_zero (e : Frame) (r : X → ℝ) (y : X) :
    normalFrameRadiusCurve e r y 0 = (y,(r y,frameVectorLinear e y)) := by simp [normalFrameRadiusCurve]
lemma normalFrameRotationCurve_zero (e : Frame) (r : X → ℝ) (y : X) (i j : I) :
    normalFrameRotationCurve e r y i j 0 = (y,(r y,frameVectorLinear e y)) := by
  have hOp : (coordinateRotationIsometry i j 0).toContinuousLinearEquiv.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro z
    change coordinateRotation i j 0 z = z
    exact coordinateRotation_zero i j z
  simp only [normalFrameRotationCurve,hOp,ContinuousLinearMap.comp_id]

lemma hasDerivAt_normalFrameActualCurve (e : Frame) (r : X → ℝ) (y a : X)
    (hr : DifferentiableAt ℝ r y) (hF : DifferentiableAt ℝ (frameVectorLinear e) y) :
    HasDerivAt (normalFrameActualCurve e r y a)
      (a,(fderiv ℝ r y a,fderiv ℝ (frameVectorLinear e) y a)) 0 := by
  have hCenter := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  change HasDerivAt (fun t : ℝ => y+t • a) _ 0 at hCenter
  simp only [one_smul,zero_add] at hCenter
  have hr' : HasFDerivAt r (fderiv ℝ r y) (y+(0:ℝ) • a) := by simpa using hr.hasFDerivAt
  have hF' : HasFDerivAt (frameVectorLinear e) (fderiv ℝ (frameVectorLinear e) y) (y+(0:ℝ) • a) := by simpa using hF.hasFDerivAt
  have hR := hr'.comp_hasDerivAt 0 hCenter
  have hFrame := hF'.comp_hasDerivAt 0 hCenter
  change HasDerivAt (fun t => r (y+t • a)) (fderiv ℝ r y a) 0 at hR
  change HasDerivAt (fun t => frameVectorLinear e (y+t • a)) (fderiv ℝ (frameVectorLinear e) y a) 0 at hFrame
  exact hCenter.prodMk (hR.prodMk hFrame)
lemma hasDerivAt_normalFrameParallelCurve (g : MetricField) (e : Frame) (r : X → ℝ) (y a : X) :
    HasDerivAt (normalFrameParallelCurve g e r y a)
      (a,(0,-((connectionBilinear g y a).comp (frameVectorLinear e y)))) 0 := by
  have hCenter := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  change HasDerivAt (fun t : ℝ => y+t • a) _ 0 at hCenter
  simp only [one_smul,zero_add] at hCenter
  exact hCenter.prodMk ((hasDerivAt_const (0:ℝ) (r y)).prodMk
    (hasDerivAt_affineParallelFrame g y a (frameVectorLinear e y) 0))
lemma hasDerivAt_normalFrameRadiusCurve (e : Frame) (r : X → ℝ) (y : X) :
    HasDerivAt (normalFrameRadiusCurve e r y) ((0:X),(r y,(0:X →L[ℝ] X))) 0 := by
  unfold normalFrameRadiusCurve
  have hRad := ((hasDerivAt_const (0:ℝ) 1).add (hasDerivAt_id (0:ℝ))).mul_const (r y)
  simpa only [normalFrameRadiusCurve,Pi.add_apply,Function.id_def,zero_add,one_mul] using (hasDerivAt_const (0:ℝ) y).prodMk
    (hRad.prodMk (hasDerivAt_const (0:ℝ) (frameVectorLinear e y)))
lemma hasDerivAt_normalFrameRotationCurve (e : Frame) (r : X → ℝ) (y : X) (i j : I) :
    HasDerivAt (normalFrameRotationCurve e r y i j)
      ((0:X),(0,(frameVectorLinear e y).comp (rotationVectorL i j))) 0 := by
  unfold normalFrameRotationCurve
  have hOp := (hasDerivAt_const (0:ℝ) (frameVectorLinear e y)).clm_comp
    (hasDerivAt_coordinateRotationOperator_zero i j)
  simpa only [normalFrameRotationCurve,ContinuousLinearMap.zero_comp,zero_add] using
    (hasDerivAt_const (0:ℝ) y).prodMk ((hasDerivAt_const (0:ℝ) (r y)).prodMk hOp)

/-- Exact tangent decomposition for an arbitrary moving radius and smooth
    orthonormal frame. The radius coefficient is its actual logarithmic jet. -/
theorem normalFrameParameter_first_jet_split (g : MetricField) (e : Frame) (r : X → ℝ) (y a : X)
    (hr : DifferentiableAt ℝ r y) (hr0 : r y ≠ 0)
    (hF : DifferentiableAt ℝ (frameVectorLinear e) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient g e y a i j = -frameConnectionCoefficient g e y a j i) :
    (a,(fderiv ℝ r y a,fderiv ℝ (frameVectorLinear e) y a)) =
      (a,(0,-((connectionBilinear g y a).comp (frameVectorLinear e y))))+
        (fderiv ℝ (fun x => Real.log (r x)) y a) • ((0:X),(r y,(0:X →L[ℝ] X)))+
        ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient g e y a i j) •
          ((0:X),(0,(frameVectorLinear e y).comp (rotationVectorL i j))) := by
  simp only [Fin.sum_univ_three,Prod.smul_mk,Prod.mk_add_mk,smul_zero,zero_add,add_zero]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change fderiv ℝ r y a = (fderiv ℝ (fun x => Real.log (r x)) y a)*r y
      rw [logRadius_derivative r y a hr hr0]
      field_simp
    · simpa only [Fin.sum_univ_three] using fderiv_frameVectorLinear_parallel_rotation_split g e y a hF he hframe hSkew

private lemma deriv_parameter_curve_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : NormalFrameParameter → E) (c : ℝ → NormalFrameParameter) (p v : NormalFrameParameter)
    (hc : HasDerivAt c v 0) (hcp : c 0 = p) (hH : DifferentiableAt ℝ H p) :
    deriv (fun t => H (c t)) 0 = fderiv ℝ H p v := by
  have hH' : HasFDerivAt H (fderiv ℝ H p) (c 0) := by rw [hcp];exact hH.hasFDerivAt
  exact (hH'.comp_hasDerivAt 0 hc).deriv

/-- For every differentiable family parametrized by center, radius and frame,
    its actual center derivative minus the frame-rotation action equals the
    parallel-center derivative plus the true logarithmic-radius derivative.
    This applies in particular to a genuine native midpoint radial family. -/
theorem deriv_normalFrame_family_covariant_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (e : Frame) (r : X → ℝ) (y a : X)
    (H : NormalFrameParameter → E)
    (hr : DifferentiableAt ℝ r y) (hr0 : r y ≠ 0)
    (hF : DifferentiableAt ℝ (frameVectorLinear e) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient g e y a i j = -frameConnectionCoefficient g e y a j i)
    (hH : DifferentiableAt ℝ H (y,(r y,frameVectorLinear e y))) :
    deriv (fun t => H (normalFrameActualCurve e r y a t)) 0-
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient g e y a i j) •
        deriv (fun t => H (normalFrameRotationCurve e r y i j t)) 0 =
      deriv (fun t => H (normalFrameParallelCurve g e r y a t)) 0+
        (fderiv ℝ (fun x => Real.log (r x)) y a) • deriv (fun t => H (normalFrameRadiusCurve e r y t)) 0 := by
  let p : NormalFrameParameter := (y,(r y,frameVectorLinear e y))
  have hA := deriv_parameter_curve_comp H (normalFrameActualCurve e r y a) p _
    (hasDerivAt_normalFrameActualCurve e r y a hr hF) (normalFrameActualCurve_zero e r y a) hH
  have hP := deriv_parameter_curve_comp H (normalFrameParallelCurve g e r y a) p _
    (hasDerivAt_normalFrameParallelCurve g e r y a) (normalFrameParallelCurve_zero g e r y a) hH
  have hR := deriv_parameter_curve_comp H (normalFrameRadiusCurve e r y) p _
    (hasDerivAt_normalFrameRadiusCurve e r y) (normalFrameRadiusCurve_zero e r y) hH
  have hO (i j : I) := deriv_parameter_curve_comp H (normalFrameRotationCurve e r y i j) p _
    (hasDerivAt_normalFrameRotationCurve e r y i j) (normalFrameRotationCurve_zero e r y i j) hH
  rw [hA,hP,hR]
  simp_rw [hO]
  have hSplit := congrArg (fderiv ℝ H p) (normalFrameParameter_first_jet_split g e r y a hr hr0 hF he hframe hSkew)
  simp only [map_add,map_sum,map_smul] at hSplit
  rw [hSplit]
  abel

end ShrinkingSpheres
