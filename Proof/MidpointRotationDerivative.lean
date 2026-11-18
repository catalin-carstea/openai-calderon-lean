import Proof.LocalMidpointRotationDerivative
import Proof.Archive.SphereSobolevConormalRotationDerivative
import Proof.CompatibleEndpointDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Differentiate genuine orthogonal covariance in the distribution space
    one order below the output. No classical generator domain is assumed. -/
theorem sphereSobolev_operator_rotation_derivative_distribution
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (i j : Fin 3)
    (Q : ℝ → SphereSobolev (s-1) →L[ℝ] SphereSobolev t)
    (Q0 C : SphereSobolev (s-1) →L[ℝ] SphereSobolev t)
    (hQ : HasDerivAt Q C 0) (hzero : Q 0 = Q0)
    (hcov : ∀ θ u,Q θ (sphereSobolevOrthogonalPullbackL (s-1)
      (coordinateRotationIsometry i j θ) u) =
      sphereSobolevOrthogonalPullbackL t (coordinateRotationIsometry i j θ) (Q0 u))
    (f : SphereSobolev s) :
    sphereSobolevRotationL t i j (Q0 (sphereSobolevInclusionL s (s-1) (by linarith) f)) =
      sphereSobolevInclusionL t (t-1) (by linarith)
        (C (sphereSobolevInclusionL s (s-1) (by linarith) f)+Q0 (sphereSobolevRotationL s i j f)) := by
  exact sphereSobolev_operator_rotation_derivative_distribution_of_germ hO hD s t i j Q Q0 C hQ hzero
    (Filter.Eventually.of_forall fun θ => hcov θ) f

/-- The actual midpoint derivative is determined by its high restriction. -/
theorem midpoint_curve_derivative_eq_of_high_restriction
    (R : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (H : ℝ → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (C : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : DifferentiableAt ℝ R 0) (hH : DifferentiableAt ℝ H 0)
    (hComp : (fun θ => (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H θ)) =ᶠ[𝓝 (0:ℝ)]
      fun θ => (R θ).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hC : C.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (deriv H 0)) :
    deriv R 0 = C := by
  have hD := clm_compatible_endpoint_derivatives R H
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) 0 hR hH hComp 1
  simp only [fderiv_apply_one_eq_deriv] at hD
  have hEq := hD.symm.trans hC.symm
  apply DFunLike.ext'
  exact (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer
    (deriv R 0).continuous C.continuous (funext fun f => congrArg (fun T => T f) hEq)

end ShrinkingSpheres
