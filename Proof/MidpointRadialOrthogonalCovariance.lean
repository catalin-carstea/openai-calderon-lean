import Proof.OrthogonalPoissonCovariance
import Proof.RadialConormalReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- Dense strong restriction transports genuine high radial covariance to
    the actual compatible H1-to-L2 radial maps. -/
theorem midpointRadial_orthogonal_covariance (e : X ≃ₗᵢ[ℝ] X)
    (F G : SmoothCoefficientMatrix 2) (R S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F))
    (hS : S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL G))
    (hHigh : (actualHighRadialErrorL G).comp (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e) =
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e).comp (actualHighRadialErrorL F)) :
    S.comp (sphereSobolevOrthogonalPullbackL 1 e) = (sphereSobolevOrthogonalPullbackL 0 e).comp R := by
  apply continuousLinearMap_eq_of_high_restriction
  intro f
  have hI := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 1 => T f)
    (sphereSobolevInclusionL_orthogonalPullback (3/2:ℝ) 1 (by norm_num) e)
  have hL := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 =>
    T (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e f)) hS
  have hH := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f) hHigh
  have hO := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev 0 =>
    T (actualHighRadialErrorL F f))
      (sphereSobolevInclusionL_orthogonalPullback (1/2:ℝ) 0 (by norm_num) e)
  have hR0 := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T f) hR
  exact (congrArg S hI.symm).trans (hL.trans
    ((congrArg (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) hH).trans
      (hO.trans (congrArg (sphereSobolevOrthogonalPullbackL 0 e) hR0.symm))))

end ShrinkingSpheres
