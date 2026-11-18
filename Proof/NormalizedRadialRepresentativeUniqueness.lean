import Proof.RadialMidpointCoefficientCongruence
import Proof.ActualMidpointRadialUniqueness
import Proof.NormalizedFirstCoefficientTaylor
import Proof.ScalarDirichletNormalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Restoring the fixed center scalar gives a genuine unnormalized actual
    coefficient representative on the same physical ball. -/
theorem normalized_coefficient_scaled_field (d : Data) (y : X) (F : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = normalizedFirstNormalCoefficient d y z) :
    ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (firstMetricDensityFactor d.γ d.g₁ y • F) z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z := by
  intro z hz
  rw [coefficientMatrixField_smul,hField z hz]
  change firstMetricDensityFactor d.γ d.g₁ y •
    ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹ • principalCoefficient
      (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z) = _
  rw [smul_smul,mul_inv_cancel₀ (firstMetricDensityFactor_pos _ _ _).ne',one_smul]

/-- Every actual radial representative equals the midpoint obtained from a
    genuine normalized coefficient and its native high restriction. -/
theorem actual_midpoint_eq_of_normalized_restriction (d : Data) (y : X)
    (R T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (F : SmoothCoefficientMatrix 2)
    (hR : RealizesActualMidpointRadialError d y R)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = normalizedFirstNormalCoefficient d y z)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hT : T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)) : R = T := by
  let c := firstMetricDensityFactor d.γ d.g₁ y
  have hRN := hR (c • F) (normalized_coefficient_scaled_field d y F hField)
  rw [actualHighRadialErrorL_const_smul F c (firstMetricDensityFactor_pos _ _ _).ne' hInv] at hRN
  exact midpoint_radial_eq_of_coefficient_restrictions R T F F (fun _ _ => rfl) hRN hT

end ShrinkingSpheres
