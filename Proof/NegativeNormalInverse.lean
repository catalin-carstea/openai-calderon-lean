import Proof.BoundaryNormalPerturbation
import Proof.ScalarOperatorInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

theorem norm_negative_normal_error_le (F F0 : SmoothCoefficientMatrix 2) (c q : ℝ) (hq : 0 ≤ q)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ q) :
    ‖negativeBoundaryCoefficientMulL (normalCoefficientJet F)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ boundaryHalfMultiplierBudget*(36*q) := by
  have hCB := normalCoefficientJet_local_C1 (F-c • F0) q hq hValue hDerivative
  have hb := norm_nativeNegativeHalfCoefficientMulL_local_C1 (normalCoefficientJet (F-c • F0)) (36*q)
    (by positivity) (fun x hx => (hCB x hx).1) (fun x hx => (hCB x hx).2)
  have hEq : negativeBoundaryCoefficientMulL (normalCoefficientJet F)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ))) =
      negativeBoundaryCoefficientMulL (normalCoefficientJet (F-c • F0)) := by
    have h := negative_normal_coefficient_decomposition F F0 c hF0
    exact (congrArg (fun T => T-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) h).trans
      (by abel)
  exact (congrArg norm hEq).le.trans hb

theorem norm_negative_tangent_coefficient_le (F F0 : SmoothCoefficientMatrix 2) (c q : ℝ) (hq : 0 ≤ q)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ q)
    (j : I) :
    ‖negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)‖ ≤ boundaryHalfMultiplierBudget*(78*q) := by
  have hCB := tangentCoefficientJet_local_C1 (F-c • F0) q hq hValue hDerivative j
  have hb := norm_nativeNegativeHalfCoefficientMulL_local_C1 (tangentCoefficientJet (F-c • F0) j) (78*q)
    (by positivity) (fun x hx => (hCB x hx).1) (fun x hx => (hCB x hx).2)
  exact (congrArg norm (negative_tangent_coefficient_decomposition F F0 c hF0 j)).le.trans hb

/-- A common local C1 perturbation bound gives the reciprocal-scale inverse
    estimate for the actual negative-half normal coefficient operator. -/
theorem norm_negative_normal_inverse_le (F F0 : SmoothCoefficientMatrix 2) (c q lam Lam : ℝ)
    (hc : 0 < c) (hq : 0 ≤ q)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X) (coefficientMatrixField 2 F) lam Lam)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ q)
    (hSmall : c⁻¹*(boundaryHalfMultiplierBudget*(36*q)) ≤ (1/2:ℝ)) :
    ‖(negativeBoundaryCoefficientMulL (normalCoefficientJet F)).inverse‖ ≤ 2*c⁻¹ := by
  have hA := negativeNormalCoefficient_isInvertible F (normalCoefficientJet F)
    (coefficientSmoothData_normalCoefficientJet F) lam Lam hUE
  obtain ⟨hA0,hInv0⟩ := scalar_identity_inverse_data (SphereSobolev (-(1/2:ℝ))) c hc
  have hDiff := norm_negative_normal_error_le F F0 c q hq hF0 hValue hDerivative
  exact inverse_norm_le_twice_of_half_perturbation
    (negativeBoundaryCoefficientMulL (normalCoefficientJet F))
    (c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) hA hA0 c⁻¹ (inv_nonneg.mpr hc.le) hInv0
      ((mul_le_mul_of_nonneg_left hDiff (inv_nonneg.mpr hc.le)).trans hSmall)

end ShrinkingSpheres
