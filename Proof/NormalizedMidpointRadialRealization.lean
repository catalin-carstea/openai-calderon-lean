import Proof.NormalizedRadialRepresentativeUniqueness
import Proof.ScalarDirichletNormalization
import Proof.NormalizedFirstCoefficientTaylor
import Proof.ActualMidpointRadialUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Normalized actual coefficient representatives specify the unchanged
    physical radial response through their genuine dense endpoint restriction. -/
theorem realizesActualMidpointRadialError_of_normalized_restriction
    (d : Data) (y : X) (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (F : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = normalizedFirstNormalCoefficient d y z)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)) :
    RealizesActualMidpointRadialError d y R := by
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let G := c • F
  have hc : c ≠ 0 := (firstMetricDensityFactor_pos _ _ _).ne'
  have hHigh := actualHighRadialErrorL_const_smul F c hc hInv
  have hG (z : X) (hzB : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 G z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z :=
    normalized_coefficient_scaled_field d y F hField z hzB
  have hActual : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL G) :=
    hR.trans (congrArg (fun T => (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp T) hHigh.symm)
  exact realizesActualMidpointRadialError_of_restriction d y R G hG hActual

end ShrinkingSpheres
