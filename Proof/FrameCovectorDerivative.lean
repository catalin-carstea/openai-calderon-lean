import Proof.MovingFrameSecond
import Proof.HessianDifferential
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The derivative of df in a moving frame has exactly its logarithmic or
    ordinary Hessian after the tensor-index connection is subtracted. -/
lemma frame_covector_derivative_eq_hessian (g : MetricField) (e : Frame) (f : X → ℝ)
    (y a : X) (j : I) (hf : DifferentiableAt ℝ (fderiv ℝ f) y)
    (he : DifferentiableAt ℝ (fun x => e x j) y)
    (hFrame : ∀ i k,metricPair g y (e y i) (e y k)=if i=k then 1 else 0) :
    fderiv ℝ (fun x => fderiv ℝ f x (e x j)) y a-
      ∑ k : I,frameConnectionCoefficient g e y a j k*fderiv ℝ f y (e y k)=
      hessianBilinear g f y a (e y j) := by
  have hPair := hf.hasFDerivAt.clm_apply he.hasFDerivAt
  have hActual : fderiv ℝ (fun x => fderiv ℝ f x (e x j)) y a=
      fderiv ℝ (fderiv ℝ f) y a (e y j)+fderiv ℝ f y (fderiv ℝ (fun x => e x j) y a) := by
    have hh := DFunLike.congr_fun hPair.fderiv a
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,add_comm] using hh
  have hReconstruct := congrArg (fderiv ℝ f y) (frame_connection_reconstruct g e y a hFrame j)
  simp only [map_sum,map_smul,smul_eq_mul,covariantFrameVector,map_add] at hReconstruct
  rw [hActual,hessianBilinear_apply]
  linarith only [hReconstruct]
end ShrinkingSpheres
