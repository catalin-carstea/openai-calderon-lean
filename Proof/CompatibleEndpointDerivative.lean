import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Basic
import Proof.Archive.SphereSobolevMidpointExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 30
open Filter
open scoped Topology
namespace ShrinkingSpheres

/-- A genuine local endpoint compatibility identity is inherited by the same
    actual operator derivatives, before midpoint interpolation is applied. -/
theorem clm_compatible_endpoint_derivatives
    {P A B C D : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (L : P → B →L[ℝ] D) (H : P → A →L[ℝ] C)
    (J : C →L[ℝ] D) (K : A →L[ℝ] B) (x : P)
    (hL : DifferentiableAt ℝ L x) (hH : DifferentiableAt ℝ H x)
    (hCompatible : (fun p => J.comp (H p)) =ᶠ[𝓝 x] fun p => (L p).comp K) (v : P) :
    J.comp (fderiv ℝ H x v) = (fderiv ℝ L x v).comp K := by
  let Post : (A →L[ℝ] C) →L[ℝ] (A →L[ℝ] D) := ContinuousLinearMap.compL ℝ A C D J
  let Pre : (B →L[ℝ] D) →L[ℝ] (A →L[ℝ] D) := (ContinuousLinearMap.compL ℝ A B D).flip K
  have hLeft : HasFDerivAt (fun p => J.comp (H p)) (Post.comp (fderiv ℝ H x)) x :=
    Post.hasFDerivAt.comp x hH.hasFDerivAt
  have hRight : HasFDerivAt (fun p => (L p).comp K) (Pre.comp (fderiv ℝ L x)) x :=
    Pre.hasFDerivAt.comp x hL.hasFDerivAt
  have hSame := hLeft.unique (hRight.congr_of_eventuallyEq hCompatible)
  exact congrArg (fun Q : P →L[ℝ] A →L[ℝ] D => Q v) hSame

open OAI.AnisotropicCalderon.SphereHarmonic

/-- Compatible true endpoint derivatives with quadratic norms interpolate to
    a quadratic H1-to-L2 operator, with the actual high derivative restriction. -/
theorem exists_midpoint_of_compatible_endpoint_derivatives
    (L : ℝ → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ))
    (H : ℝ → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hL : DifferentiableAt ℝ L 0) (hH : DifferentiableAt ℝ H 0)
    (hCompatible : (fun θ => (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp (H θ)) =ᶠ[𝓝 (0:ℝ)]
      fun θ => (L θ).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (CL CH r : ℝ) (hLN : ‖fderiv ℝ L 0‖ ≤ CL*r^2) (hHN : ‖fderiv ℝ H 0‖ ≤ CH*r^2) :
    ∃ C : SphereSobolev 1 →L[ℝ] SphereSobolev 0,‖C‖ ≤ ((CL+CH)/2)*r^2 ∧
      C.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (deriv H 0) := by
  have hD := clm_compatible_endpoint_derivatives L H
    (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) 0 hL hH hCompatible 1
  simp only [fderiv_apply_one_eq_deriv] at hD
  let C := sphereSobolevMidpointL (deriv L 0) (deriv H 0) hD
  have hLo : ‖deriv L 0‖ ≤ CL*r^2 := norm_deriv_eq_norm_fderiv.le.trans hLN
  have hHi : ‖deriv H 0‖ ≤ CH*r^2 := norm_deriv_eq_norm_fderiv.le.trans hHN
  refine ⟨C,?_,sphereSobolevMidpointL_inclusion (deriv L 0) (deriv H 0) hD⟩
  exact (norm_sphereSobolevMidpointL_le (deriv L 0) (deriv H 0) hD).trans (by
    have hSum := add_le_add hLo hHi
    nlinarith only [hSum])

end ShrinkingSpheres
