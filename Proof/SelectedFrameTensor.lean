import Proof.FrameTensorOperatorCombination
import Proof.FrameErrorCovariantTensor
import Proof.CoarseCovariantJetFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual tensor graph uniquely fixes its coarse witness, so endpoint
    transport retains ANY already selected physical second-trace tensor. -/
lemma selected_frame_tensor_eq (d : Data)
    (F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → X → X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0))
    (y b : X) (j : I) (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hFS : ∀ a,DifferentiableAt ℝ (F a) y)
    (he : DifferentiableAt ℝ (fun x => d.frame x j) y)
    (hFrame : ∀ k l,metricPair d.γ y (d.frame y k) (d.frame y l)=if k=l then 1 else 0)
    (hS : ∀ a,CoarseCovariantRotationGraph d y b (F a) (S a y b))
    (hT : CoarseCovariantRotationGraph d y b (fun x => ∑ a : I,d.frame x j a • F a x)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y b j k •
        (∑ a : I,d.frame y k a • F a y))+T)) :
    T=frameTensorOperatorCombination d y b j (fun a => F a y) (fun a => S a y b) := by
  have h := coarseCovariantRotationGraph_unique hT
    (frameWeighted_covariant_graph d F S y b j hFS he hFrame hS)
  have hEq : T=frameWeightedCovariantTensorJet d F S y b j := add_left_cancel h
  exact hEq
end ShrinkingSpheres
