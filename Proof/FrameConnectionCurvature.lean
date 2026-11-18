import Proof.GaugedConnectionCurvature
import Proof.FrameCurveFirstJet
import Proof.FrameCoordinatesLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- The finite-dimensional coordinate-frame connection whose infinitesimal
rotation action appears in the actual angular covariant derivative. -/
def frameConnectionOperator (g : MetricField) (e : Frame) (y : X) : X →L[ℝ] X →L[ℝ] X :=
  ∑ i : I,∑ j : I,((1/2:ℝ) • frameConnectionLinear g e y i j).smulRight (rotationVectorL i j)

lemma frameConnectionOperator_apply (g : MetricField) (e : Frame) (y a : X) :
    frameConnectionOperator g e y a=
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient g e y a i j) • rotationVectorL i j := by
  simp only [frameConnectionOperator,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,frameConnectionLinear_apply,smul_eq_mul]

lemma Elliptic.contDiffOn_frameConnectionOperator {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g : MetricField} (hg : Elliptic Y K g) (hK : 0 < K)
    (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y) :
    ContDiffOn ℝ ∞ (frameConnectionOperator g e) Y := by
  have hΓ (i j : I) : ContDiffOn ℝ ∞ (fun x => frameConnectionLinear g e x i j) Y := by
    apply contDiffOn_clm_apply.mpr
    intro a
    simpa only [frameConnectionLinear_apply] using
      hg.contDiffOn_frameConnection hY hK e he (fun _ => a) contDiffOn_const i j
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    ((hΓ i j).const_smul (1/2:ℝ)).smulRight contDiffOn_const))

lemma frameConnectionOperator_transport (g : MetricField) (e : Frame) (y a : X)
    (hL : DifferentiableAt ℝ (frameVectorLinear e) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient g e y a i j= -frameConnectionCoefficient g e y a j i) :
    fderiv ℝ (frameVectorLinear e) y a=
      (frameVectorLinear e y).comp (frameConnectionOperator g e y a)-
        (connectionBilinear g y a).comp (frameVectorLinear e y) := by
  have hComp : (frameVectorLinear e y).comp (frameConnectionOperator g e y a)=
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient g e y a i j) •
        (frameVectorLinear e y).comp (rotationVectorL i j) := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [frameConnectionOperator_apply,ContinuousLinearMap.comp_apply,
      _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  rw [hComp]
  exact (fderiv_frameVectorLinear_parallel_rotation_split g e y a hL he hFrame hSkew).trans (by abel)

/-- The curvature of the actual moving-frame connection is the actual
reference curvature in that frame. Arbitrary frame derivatives cancel. -/
theorem Elliptic.frameConnectionOperator_curvature_intertwine {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g : MetricField} (hg : Elliptic Y K g) (hK : 0 < K)
    (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j)=if i=j then 1 else 0)
    {y : X} (hy : y ∈ Y) (a b : X) :
    (frameVectorLinear e y).comp (curvatureLinear (frameConnectionOperator g e) y a b)=
      (curvatureLinear (connectionBilinear g) y a b).comp (frameVectorLinear e y) := by
  have hL : ContDiffOn ℝ ∞ (frameVectorLinear e) Y := fun x hx =>
    (contDiffAt_frameVectorLinear e x (fun i => (he i).contDiffAt (hY.mem_nhds hx))).contDiffWithinAt
  exact gauged_connection_curvature_intertwine hY (connectionBilinear g) (frameConnectionOperator g e)
    (frameVectorLinear e) (hg.contDiffOn_connectionBilinear hY hK)
    (hg.contDiffOn_frameConnectionOperator hY hK e he) hL
    (fun x hx a => frameConnectionOperator_transport g e x a
      ((hL.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      (fun i => ((he i).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      (hFrame x hx) (frameConnection_skew hY hg hK e he hFrame hx a)) hy a b

lemma Elliptic.frameConnectionOperator_curvature_coordinate {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g : MetricField} (hg : Elliptic Y K g) (hK : 0 < K)
    (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j)=if i=j then 1 else 0)
    {y : X} (hy : y ∈ Y) (a b : X) (i j : I) :
    curvatureLinear (frameConnectionOperator g e) y a b (axis i) j=
      frameCurvatureCoefficient g e y a b i j := by
  have hIntertwine := DFunLike.congr_fun
    (hg.frameConnectionOperator_curvature_intertwine hY hK e he hFrame hy a b) (axis i)
  have hPair := congrArg (fun v => frameCoordinateLinear g e y j v) hIntertwine
  have hCoordinate (z : X) : frameCoordinateLinear g e y j (frameVectorLinear e y z)=z j := by
    have hh := congrArg (fun v : X => v j) (frameCoordinatesLinear_frameVector g e y z (hFrame y hy))
    simpa only [frameCoordinatesLinear_apply,frameVectorLinear_apply] using hh
  simp only [ContinuousLinearMap.comp_apply] at hPair
  rw [hCoordinate] at hPair
  simpa only [frameVectorLinear_apply,frameVector_axis,
    curvatureLinear_apply,frameCoordinateLinear_apply,frameCurvatureCoefficient,metricCurvature] using hPair

end ShrinkingSpheres
