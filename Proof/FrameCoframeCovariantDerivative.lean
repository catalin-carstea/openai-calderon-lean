import Proof.FrameCoordinateCovectors
import Proof.MovingFrameSecond
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Ordinary derivatives of coframe coefficients split into the true frame
    connection action and the connection of the fixed physical direction. -/
lemma frameCoordinateLinear_covariant_derivative {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K)
    (e : Frame) (he : ∀ j,ContDiffOn ℝ ∞ (fun x => e x j) Ω)
    {y : X} (hy : y ∈ Ω)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (a b : X) (j : I) :
    fderiv ℝ (fun x => frameCoordinateLinear g e x j b) y a-
      ∑ k : I,frameConnectionCoefficient g e y a j k*frameCoordinateLinear g e y k b=
      frameCoordinateLinear g e y j (connection g y a b) := by
  have hD := metric_pair_fderiv hΩ h hy (fun _ => b) (fun x => e x j)
    (differentiableAt_const _) (((he j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) a
  have hC := connection_metric hΩ h hK hy a b (e y j)
  have hF := congrArg (metricBilinear g y b) (frame_connection_reconstruct g e y a hFrame j)
  have hFun : (fun x => frameCoordinateLinear g e x j b)=(fun x => metricPair g x b (e x j)) := by
    funext x
    exact frameCoordinateLinear_apply g e x b j
  rw [hFun]
  simp only [frameCoordinateLinear_apply,covariantFrameVector,← metricBilinear_apply,map_sum,map_smul,
    map_add,smul_eq_mul,fderiv_const_apply,zero_apply,map_zero,zero_add,add_zero] at hD hC hF ⊢
  linarith only [hD,hC,hF]
end ShrinkingSpheres
