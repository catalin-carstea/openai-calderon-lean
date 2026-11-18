import Proof.CoordinateRotationOperatorDerivative
import Proof.RadialCorrectionRotationCommutator
import Proof.CoordinateRotationGenerator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.MetricOperator

/-- The actual rotated covector's operator-norm derivative is its canonical
    infinitesimal rotation action. -/
theorem hasDerivAt_rotated_covector_zero (q : X →L[ℝ] ℝ) (i j : I) :
    HasDerivAt (fun θ => q.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)
      (rotationCovector q i j) 0 := by
  have h := hasDerivAt_coordinateRotationOperator_zero i j
  have hQ := (hasDerivAt_const (0:ℝ) q).clm_comp h
  have hCov : q.comp (rotationVectorL i j) = rotationCovector q i j := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply,rotationVectorL_apply,rotationVector,rotationCovector,
      map_sub,map_smul,_root_.sub_apply,_root_.smul_apply,PiLp.proj_apply,smul_eq_mul,axis]
    ring
  simpa only [ContinuousLinearMap.zero_comp,zero_add,hCov] using hQ

/-- The genuine first radial rotation derivative is exactly the already
    proved H1-domain angular commutator of its canonical first correction. -/
theorem hasDerivAt_firstRadial_rotation_zero (c : ℝ) (ell : X →L[ℝ] ℝ) (i j : I) :
    HasDerivAt (fun θ => coarseFirstRadialVariationL c
      (ell.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap))
      (radialCorrectionCovectorL (rotationCovector (c⁻¹ • ell) i j)) 0 := by
  have h := radialCorrectionCovectorL.hasFDerivAt.comp_hasDerivAt (0:ℝ)
    (hasDerivAt_rotated_covector_zero (c⁻¹ • ell) i j)
  have hFun : (fun θ => coarseFirstRadialVariationL c
      (ell.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)) =
      fun θ => radialCorrectionCovectorL ((c⁻¹ • ell).comp
        (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap) := by
    funext θ
    rw [coarseFirstRadialVariationL_normalized_covector,ContinuousLinearMap.smul_comp]
  rw [hFun]
  exact h

theorem firstRadial_rotation_derivative_commutator (c : ℝ) (ell : X →L[ℝ] ℝ) (i j : I) :
    (deriv (fun θ => coarseFirstRadialVariationL c
      (ell.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)) 0).comp
        (sphereSobolevInclusionL 1 0 (by norm_num)) =
      (sphereSobolevRotationL 1 i j).comp (radialCorrectionSobolevL 1 (c⁻¹ • ell))-
        (coarseFirstRadialVariationL c ell).comp (sphereSobolevRotationL 1 i j) := by
  rw [(hasDerivAt_firstRadial_rotation_zero c ell i j).deriv,coarseFirstRadialVariationL_normalized_covector]
  exact (rotation_radialCorrection_commutator i j (c⁻¹ • ell)).symm

end ShrinkingSpheres
