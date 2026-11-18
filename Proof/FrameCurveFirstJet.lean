import Proof.FramePullback
import Proof.CoordinateRotationGenerator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- The actual frame operator is smooth wherever its frame vectors are. -/
lemma contDiffAt_frameVectorLinear (e : Frame) (y : X)
    (he : ∀ i,ContDiffAt ℝ ∞ (fun x => e x i) y) :
    ContDiffAt ℝ ∞ (frameVectorLinear e) y := by
  exact ContDiffAt.sum fun i (_hi : i ∈ Finset.univ) => contDiffAt_const.smulRight (he i)

/-- Evaluation of the actual operator derivative recovers the derivative
    of the actual frame vectors, with no bound on those derivatives. -/
lemma fderiv_frameVectorLinear_apply (e : Frame) (y a z : X)
    (hF : DifferentiableAt ℝ (frameVectorLinear e) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y) :
    fderiv ℝ (frameVectorLinear e) y a z = ∑ i,z i • fderiv ℝ (fun x => e x i) y a := by
  let Eval : (X →L[ℝ] X) →L[ℝ] X := ContinuousLinearMap.apply ℝ X z
  have hEval := Eval.hasFDerivAt.comp y hF.hasFDerivAt
  have hs := HasFDerivAt.sum (u:=Finset.univ) (fun i _ => (he i).hasFDerivAt.const_smul (z i))
  change HasFDerivAt (fun x => ∑ i,z i • e x i) (∑ i,z i • fderiv ℝ (fun x => e x i) y) y at hs
  have hs' : HasFDerivAt (fun x => frameVectorLinear e x z)
      (∑ i,z i • fderiv ℝ (fun x => e x i) y) y := by
    simpa only [frameVectorLinear_apply,frameVector] using hs
  have hh := congrArg (fun L : X →L[ℝ] X => L a) (hs'.unique hEval)
  simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,Eval] using hh.symm

/-- The ordinary frame jet splits exactly into its parallel jet and its
    connection rotation. This identity removes arbitrary frame derivatives
    from the covariant center calculation. -/
theorem fderiv_frameVectorLinear_parallel_split (g : MetricField) (e : Frame) (y a z : X)
    (hF : DifferentiableAt ℝ (frameVectorLinear e) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    fderiv ℝ (frameVectorLinear e) y a z = -connection g y a (frameVectorLinear e y z)-
      frameVectorLinear e y (frameAngularVector (frameConnectionCoefficient g e y a) z) := by
  have hAngular := frameVector_frameAngularVector g e y a z hframe
  have hGamma : connection g y a (frameVectorLinear e y z) =
      ∑ i,z i • connection g y a (e y i) := by
    simp only [frameVectorLinear_apply,frameVector,← connectionBilinear_apply,map_sum,map_smul]
  simp only [frameVectorLinear_apply] at hGamma ⊢
  rw [hAngular]
  rw [fderiv_frameVectorLinear_apply e y a z hF he]
  simp only [covariantFrameVector,smul_add,Finset.sum_add_distrib] at *
  rw [hGamma]
  abel

/-- In three dimensions the same frame jet is the sum of the parallel jet
    and the nine canonical coordinate-rotation generators. No derivative
    bounds for the chosen orthonormal frame are assumed. -/
theorem fderiv_frameVectorLinear_parallel_rotation_split (g : MetricField) (e : Frame) (y a : X)
    (hF : DifferentiableAt ℝ (frameVectorLinear e) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient g e y a i j = -frameConnectionCoefficient g e y a j i) :
    fderiv ℝ (frameVectorLinear e) y a = -((connectionBilinear g y a).comp (frameVectorLinear e y))+
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient g e y a i j) •
        (frameVectorLinear e y).comp (rotationVectorL i j) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [fderiv_frameVectorLinear_parallel_split g e y a z hF he hframe,
    frameAngularVector_eq_rotation _ hSkew]
  simp only [map_sum,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply,connectionBilinear_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,rotationVectorL_apply]
  simp only [neg_mul,neg_smul,Finset.sum_neg_distrib]
  abel

end ShrinkingSpheres
