import Proof.LocalMidpointRotationDerivative
import Proof.RadialRotationCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Subtracting the canonical first correction from a covariant radial
    family leaves precisely its bounded quadratic derivative as commutator. -/
theorem radial_taylor_rotation_commutator_distribution_of_germ
    (i j : I) (r : ℝ)
    (R : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (DR C : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (B0 D : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (B1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (hR : HasDerivAt R DR 0)
    (hCov : ∀ᶠ θ in 𝓝 (0:ℝ),∀ u,R θ (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ) u) =
      sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ) (R 0 u))
    (hCompat : ∀ v,sphereSobolevInclusionL 1 0 (by norm_num) (B1 v) =
      B0 (sphereSobolevInclusionL 1 0 (by norm_num) v))
    (hComm : (sphereSobolevRotationL 1 i j).comp B1-B0.comp (sphereSobolevRotationL 1 i j) =
      D.comp (sphereSobolevInclusionL 1 0 (by norm_num)))
    (hC : C = DR-r • D.comp (sphereSobolevInclusionL 1 0 (by norm_num)))
    (f : SphereSobolev 2) :
    let P := R 0-r • B0.comp (sphereSobolevInclusionL 1 0 (by norm_num))
    sphereSobolevRotationL 0 i j (P (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+P (sphereSobolevRotationL 2 i j f)) := by
  have hTotal : sphereSobolevRotationL 0 i j (R 0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (DR (sphereSobolevInclusionL 2 1 (by norm_num) f)+R 0 (sphereSobolevRotationL 2 i j f)) := by
    have h := sphereSobolev_operator_rotation_derivative_distribution_of_germ orthogonalSphereHarmonics denseSphereHarmonics
      2 0 i j R (R 0) DR hR rfl hCov f
    have hI : sphereSobolevInclusionL 2 ((2:ℝ)-1) (by norm_num) =
        sphereSobolevInclusionL 2 1 (by norm_num) := by congr 1 <;> norm_num
    have hJ : sphereSobolevInclusionL 0 ((0:ℝ)-1) (by norm_num) =
        sphereSobolevInclusionL 0 (-1) (by norm_num) := by congr 1 <;> norm_num
    rw [hI,hJ] at h
    exact h
  have hFirst := first_radial_rotation_commutator_distribution i j B0 D B1 hCompat hComm f
  dsimp only
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    map_sub,map_smul,hTotal,hFirst,hC,map_add]
  module

end ShrinkingSpheres
