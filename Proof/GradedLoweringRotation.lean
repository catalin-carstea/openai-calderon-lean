import Proof.FlatLoweringSobolev
import Proof.RadialCorrectionRotationBlocks
import Proof.GradedRaisingRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.HarmonicDerivativeOperator
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

lemma flatLoweringSobolevL_rotation_commutator (s : ℝ) (i j a : I) :
    (sphereSobolevRotationL (s-1) i j).comp (flatLoweringSobolevL s a)-
      (flatLoweringSobolevL (s-1) a).comp (sphereSobolevRotationL s i j)=
    (sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)).comp
      ((if a=j then flatLoweringSobolevL s i else 0)-(if a=i then flatLoweringSobolevL s j else 0)) := by
  apply sphereSobolev_clm_eq_of_single s
  intro k z
  cases k with
  | zero =>
    simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,sphereSobolevRotationL_single,
      flatLoweringSobolevL_single_zero,map_zero,sub_zero,clm_ite_zero_apply,clm_apply_ite_zero,
      _root_.zero_apply,ite_self,sub_self]
  | succ k =>
    simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,
      sphereSobolevRotationL_single,flatLoweringSobolevL_single_succ]
    have hh := congrArg (sphereSobolevSingleL ((s-1)-1) k)
      (harmonicRotation_derivative_commutator k i j a z)
    simp only [map_sub,clm_apply_ite_zero] at hh
    simpa only [map_sub,clm_ite_zero_apply,clm_apply_ite_zero,_root_.zero_apply,
      flatLoweringSobolevL_single_succ,sphereSobolevInclusionL_single] using hh

end ShrinkingSpheres
