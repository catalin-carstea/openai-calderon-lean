import Proof.HarmonicRaisingRotation
import Proof.FlatRaisingHigherAlgebra
import Proof.RotationContractionAlgebra
import Proof.Archive.SphereSobolevSingleRotationAngleDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.HarmonicDerivativeOperator
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection OAI.AnisotropicCalderon.RotationLieAlgebra

/-- The rotation/raising commutator loses only one true angular order.
    Its two compositions are compared in their genuine common lower space. -/
lemma flatRaisingSobolevL_rotation_commutator (s : ℝ) (i j a : I) :
    (sphereSobolevRotationL (s-1) i j).comp (flatRaisingSobolevL s a)-
      (flatRaisingSobolevL (s-1) a).comp (sphereSobolevRotationL s i j)=
    (sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)).comp
      ((if a=j then flatRaisingSobolevL s i else 0)-(if a=i then flatRaisingSobolevL s j else 0)) := by
  apply sphereSobolev_clm_eq_of_single s
  intro k z
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,
    sphereSobolevRotationL_single,flatRaisingSobolevL_single]
  have hh := congrArg (sphereSobolevSingleL ((s-1)-1) (k+1))
    (harmonicSphereRotation_raising_commutator sphereFischerInner k i j a z)
  simp only [map_sub,clm_apply_ite_zero] at hh
  simpa only [map_sub,clm_ite_zero_apply,clm_apply_ite_zero,_root_.zero_apply,
    flatRaisingSobolevL_single,sphereSobolevInclusionL_single] using hh
end ShrinkingSpheres
