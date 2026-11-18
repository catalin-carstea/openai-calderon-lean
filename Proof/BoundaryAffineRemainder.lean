import Proof.BoundaryAffineCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The scalar affine model contributes no tangential conormal coefficient,
    so the actual tangential coefficient is quadratically small. -/
theorem norm_negative_tangent_affine_remainder_le (F F0 F1 : SmoothCoefficientMatrix 2)
    (c r q : ℝ) (hq : 0 ≤ q) (s : X → ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = s w.val • (1:Mat))
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ q)
    (j : I) :
    ‖negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)‖ ≤ boundaryHalfMultiplierBudget*(78*q) := by
  have hC1 := tangentCoefficientJet_local_C1 (F-c • F0-r • F1) q hq hValue hDerivative j
  have hb := norm_nativeNegativeHalfCoefficientMulL_local_C1 (tangentCoefficientJet (F-c • F0-r • F1) j)
    (78*q) (by positivity) (fun x hx => (hC1 x hx).1) (fun x hx => (hC1 x hx).2)
  have hEq : negativeBoundaryCoefficientMulL (tangentCoefficientJet (F-c • F0-r • F1) j) =
      negativeBoundaryCoefficientMulL (tangentCoefficientJet F j) := by
    rw [negativeTangentCoefficient_sub_smul,negativeTangentCoefficient_scalar_zero F1 s hF1 j,smul_zero,sub_zero,
      ← negative_tangent_coefficient_decomposition F F0 c hF0 j]
  change ‖negativeBoundaryCoefficientMulL (tangentCoefficientJet (F-c • F0-r • F1) j)‖ ≤ _ at hb
  rw [hEq] at hb
  exact hb

/-- Local C1 control of the affine coefficient controls its normal first variation. -/
theorem norm_negative_first_normal_coefficient_le (F1 : SmoothCoefficientMatrix 2) (P : ℝ) (hP : 0 ≤ P)
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P) :
    ‖negativeBoundaryCoefficientMulL (normalCoefficientJet F1)‖ ≤ boundaryHalfMultiplierBudget*(36*P) := by
  have hC1 := normalCoefficientJet_local_C1 F1 P hP hValue hDerivative
  exact norm_nativeNegativeHalfCoefficientMulL_local_C1 (normalCoefficientJet F1) (36*P)
    (by positivity) (fun x hx => (hC1 x hx).1) (fun x hx => (hC1 x hx).2)

/-- The affine normal model also gives the linear perturbation size needed
    for its common normal inverse bound. -/
theorem norm_normal_first_difference_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M M1 : E →L[ℝ] E) (c r QM CM : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hQM : 0 ≤ QM) (hCM : 0 ≤ CM)
    (hR : ‖M-c • ContinuousLinearMap.id ℝ E-r • M1‖ ≤ QM*r^2) (hM1 : ‖M1‖ ≤ CM) :
    ‖M-c • ContinuousLinearMap.id ℝ E‖ ≤ (QM+CM)*r := by
  have hEq : M-c • ContinuousLinearMap.id ℝ E = (M-c • ContinuousLinearMap.id ℝ E-r • M1)+r • M1 := by abel
  rw [hEq]
  calc
    _ ≤ ‖M-c • ContinuousLinearMap.id ℝ E-r • M1‖+‖r • M1‖ := norm_add_le _ _
    _ = ‖M-c • ContinuousLinearMap.id ℝ E-r • M1‖+r*‖M1‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    _ ≤ QM*r^2+r*CM := add_le_add hR (mul_le_mul_of_nonneg_left hM1 hr)
    _ ≤ QM*r+r*CM := by gcongr;nlinarith only [mul_le_mul_of_nonneg_left hr1 hr]
    _ = _ := by ring

end ShrinkingSpheres
