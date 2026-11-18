import Proof.HalfFamilyDerivativeCalculus
import Proof.GradedAdjointCovariantPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma half_covariant_adjoint_pairing (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    {y : X} (hC : ContDiffAt ℝ ∞ C y) (a : X)
    (hH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A y)=
      (C y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u v : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      (halfOperatorCovariantDerivativeL d (fun x => (C x).adjoint) A y a v)=
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
      (halfOperatorCovariantDerivativeL d C H y a u) := by
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hCA : ContDiffAt ℝ ∞ (fun x => (C x).adjoint) y := Adj.contDiff.contDiffAt.comp y hC
  simp only [halfOperatorCovariantDerivativeL,directional_half_family_comp_fixed C hC a,
    directional_half_family_comp_fixed (fun x => (C x).adjoint) hCA a,directional_half_family_adjoint C hC a]
  exact graded_adjoint_covariant_pairing _ _ _ _ _ _ _ _ sphereSobolevHalfNegativeInclusion_adjoint
    (frameAngularConnectionHalfL_adjoint d y a) hH hA (frameAngularConnectionHigherL_compatible d y a) u v
end ShrinkingSpheres
