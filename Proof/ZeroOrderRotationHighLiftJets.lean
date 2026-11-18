import Proof.ZeroOrderRotationHighLift
import Proof.RotationHighLiftJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Reconstruction on normalized weighted coordinates is the SAME fixed
linear operation at these orders. Only its jet/norm bound is reused;
physical compatibility uses zeroOrderRotationHighLiftL_compatible. -/
lemma smoothFiniteJetBound_zero_order_rotation_high_lift
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (G : I × I → P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (p : P) (N : ℕ) (B : ℝ) (hf : SmoothFiniteJetBound F p N B)
    (hg : ∀ ij,SmoothFiniteJetBound (G ij) p N B) :
    SmoothFiniteJetBound (fun x => zeroOrderRotationHighLiftL (F x) (fun i j => G (i,j) x)) p N
      ((19+9*Real.sqrt 2)*B) := by
  simpa only [rotationHighLiftDataL_apply,zeroOrderRotationHighLiftL,sphereSobolevRotationCommutatorHighLiftL] using
    smoothFiniteJetBound_rotation_high_lift F G p N B hf hg
end ShrinkingSpheres
