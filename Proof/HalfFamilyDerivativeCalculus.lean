import Proof.CovariantHalfOperatorGreen
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma directional_half_family_comp_fixed
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {y : X} (hC : ContDiffAt ℝ ∞ C y) (a : X) :
    directionalFDeriv a (fun x => (C x).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) y=
    (directionalFDeriv a C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have h := (hC.differentiableAt (by simp)).hasFDerivAt.clm_comp (hasFDerivAt_const J y)
  unfold directionalFDeriv
  rw [h.fderiv]
  simp only [directionalFDeriv,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,_root_.zero_apply,ContinuousLinearMap.comp_zero,zero_add]
  rfl

lemma directional_half_family_adjoint
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {y : X} (hC : ContDiffAt ℝ ∞ C y) (a : X) :
    directionalFDeriv a (fun x => (C x).adjoint) y=(directionalFDeriv a C y).adjoint := by
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have h := Adj.hasFDerivAt.comp y (hC.differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (fun x => Adj (C x)) (Adj.comp (fderiv ℝ C y)) y at h
  change directionalFDeriv a (fun x => Adj (C x)) y=Adj (directionalFDeriv a C y)
  simp only [directionalFDeriv,h.fderiv,ContinuousLinearMap.comp_apply]
end ShrinkingSpheres
