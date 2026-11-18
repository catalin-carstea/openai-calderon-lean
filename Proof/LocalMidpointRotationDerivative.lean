import Proof.Archive.SphereSobolevConormalRotationDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- The distributional covariance differentiation argument is local at zero;
    a genuine equality of germs suffices. -/
theorem clm_covariance_derivative_unique_of_germ
    {U V W : Type*} [NormedAddCommGroup U] [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ U] [NormedSpace ℝ V] [NormedSpace ℝ W]
    (Q : ℝ → U →L[ℝ] V) (Q0 C : U →L[ℝ] V)
    (hQ : HasDerivAt Q C 0) (hzero : Q 0 = Q0)
    (u : ℝ → U) (u0 u1 : U) (hu : HasDerivAt u u1 0) (hu0 : u 0 = u0)
    (J : V →L[ℝ] W) (z : ℝ → W) (z1 : W) (hz : HasDerivAt z z1 0)
    (hcurve : z =ᶠ[𝓝 (0:ℝ)] fun θ => J (Q θ (u θ))) :
    z1 = J (C u0+Q0 u1) := by
  have hLeft := hQ.clm_apply hu
  rw [hu0,hzero] at hLeft
  have hIncluded := J.hasFDerivAt.comp_hasDerivAt 0 hLeft
  exact hz.unique (hIncluded.congr_of_eventuallyEq hcurve)

/-- Differentiate the true local orthogonal covariance in the distribution
    space one order below the output. No global angle family is required. -/
theorem sphereSobolev_operator_rotation_derivative_distribution_of_germ
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (i j : I)
    (Q : ℝ → SphereSobolev (s-1) →L[ℝ] SphereSobolev t)
    (Q0 C : SphereSobolev (s-1) →L[ℝ] SphereSobolev t)
    (hQ : HasDerivAt Q C 0) (hzero : Q 0 = Q0)
    (hCov : ∀ᶠ θ in 𝓝 (0:ℝ),∀ u,Q θ (sphereSobolevOrthogonalPullbackL (s-1)
      (coordinateRotationIsometry i j θ) u) = sphereSobolevOrthogonalPullbackL t
        (coordinateRotationIsometry i j θ) (Q0 u))
    (f : SphereSobolev s) :
    sphereSobolevRotationL t i j (Q0 (sphereSobolevInclusionL s (s-1) (by linarith) f)) =
      sphereSobolevInclusionL t (t-1) (by linarith)
        (C (sphereSobolevInclusionL s (s-1) (by linarith) f)+Q0 (sphereSobolevRotationL s i j f)) := by
  have hInput := hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower_zero hO hD s i j f
  have hOutput := hasDerivAt_sphereSobolevOrthogonalPullback_coordinate_lower_zero hO hD t i j
    (Q0 (sphereSobolevInclusionL s (s-1) (by linarith) f))
  apply clm_covariance_derivative_unique_of_germ Q Q0 C hQ hzero
    (fun θ => sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL s (coordinateRotationIsometry i j θ) f))
    (sphereSobolevInclusionL s (s-1) (by linarith) f) (sphereSobolevRotationL s i j f) hInput
    (by rw [sphereSobolevOrthogonalPullback_coordinate_zero])
    (sphereSobolevInclusionL t (t-1) (by linarith))
    (fun θ => sphereSobolevInclusionL t (t-1) (by linarith)
      (sphereSobolevOrthogonalPullbackL t (coordinateRotationIsometry i j θ)
        (Q0 (sphereSobolevInclusionL s (s-1) (by linarith) f))))
    (sphereSobolevRotationL t i j (Q0 (sphereSobolevInclusionL s (s-1) (by linarith) f))) hOutput
  filter_upwards [hCov] with θ hθ
  have hI := congrArg (fun T => T f) (sphereSobolevInclusionL_orthogonalPullback s (s-1) (by linarith) (coordinateRotationIsometry i j θ))
  simp only [ContinuousLinearMap.comp_apply] at hI
  rw [hI]
  exact congrArg (sphereSobolevInclusionL t (t-1) (by linarith))
    (hθ (sphereSobolevInclusionL s (s-1) (by linarith) f)).symm

end ShrinkingSpheres
