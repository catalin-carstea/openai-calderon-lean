import Proof.CompatibleEndpointDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- True compatible endpoint derivative bounds control the complete
    Frechet derivative of any actual midpoint family on a local parameter set. -/
theorem norm_fderiv_midpoint_family_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ))
    (H : P → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (R : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (x : P)
    (hL : DifferentiableAt ℝ L x) (hH : DifferentiableAt ℝ H x) (hR : DifferentiableAt ℝ R x)
    (hLH : (fun p => (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp (H p)) =ᶠ[𝓝 x]
      fun p => (L p).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hRH : (fun p => (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H p)) =ᶠ[𝓝 x]
      fun p => (R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (CL CH : ℝ) (hCL : 0 ≤ CL) (hCH : 0 ≤ CH)
    (hNL : ‖fderiv ℝ L x‖ ≤ CL) (hNH : ‖fderiv ℝ H x‖ ≤ CH) :
    ‖fderiv ℝ R x‖ ≤ (CL+CH)/2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hDLow := clm_compatible_endpoint_derivatives L H
    (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) x hL hH hLH v
  have hDMid := clm_compatible_endpoint_derivatives R H
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) x hR hH hRH v
  let C := sphereSobolevMidpointL (fderiv ℝ L x v) (fderiv ℝ H x v) hDLow
  have hC := sphereSobolevMidpointL_inclusion (fderiv ℝ L x v) (fderiv ℝ H x v) hDLow
  have hEqComp := hDMid.symm.trans hC.symm
  have hEq : fderiv ℝ R x v = C := by
    apply DFunLike.ext'
    exact (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer
      (fderiv ℝ R x v).continuous C.continuous
      (funext fun f => congrArg (fun T => T f) hEqComp)
  have hLo : ‖fderiv ℝ L x v‖ ≤ CL*‖v‖ :=
    ((fderiv ℝ L x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hNL (norm_nonneg v))
  have hHi : ‖fderiv ℝ H x v‖ ≤ CH*‖v‖ :=
    ((fderiv ℝ H x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hNH (norm_nonneg v))
  rw [hEq]
  exact (norm_sphereSobolevMidpointL_le _ _ hDLow).trans (by
    have hSum := add_le_add hLo hHi
    nlinarith only [hSum])

end ShrinkingSpheres
