import Proof.SharpStrongOperator
import Proof.FullCoefficientEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Shared local affine-to-operator estimates, extracted from the original
    high radial Taylor producer for reuse by the normalized center caller. -/
theorem strong_affine_operator_point_bounds (hcalc : FixedSobolevCalculus)
    (F F0 F1 : SmoothCoefficientMatrix 2) (c r P Q : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hVal1 : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P)
    (hDeriv1 : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P)
    (hValR : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ Q*r^2)
    (hDerivR : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ Q*r^2) :
    ‖fullCoefficientOperatorL hcalc 0 F1‖ ≤ fullC1OperatorBudget hcalc*P ∧
    ‖strongDirichletOperator hcalc 0 F-strongDirichletOperator hcalc 0 (c • F0)‖ ≤ strongC1OperatorBudget hcalc*(Q+P)*r ∧
    ‖fullCoefficientOperatorL hcalc 0 F-fullCoefficientOperatorL hcalc 0 (c • F0)-
      r • fullCoefficientOperatorL hcalc 0 F1‖ ≤ (fullC1OperatorBudget hcalc*Q)*r^2 := by
  let B := fullC1OperatorBudget hcalc
  let S := strongC1OperatorBudget hcalc
  let R := F-c • F0-r • F1
  have hB : 0 ≤ B := fullC1OperatorBudget_nonneg _
  have hS : 0 ≤ S := strongC1OperatorBudget_nonneg _
  have hq : 0 ≤ Q*r^2 := mul_nonneg hQ (sq_nonneg _)
  have hT1 : ‖fullCoefficientOperatorL hcalc 0 F1‖ ≤ B*P := norm_fullCoefficientOperator_zero_le hcalc F1 P hP hVal1 hDeriv1
  have hS1 : ‖strongDirichletOperator hcalc 0 F1‖ ≤ S*P := norm_strongDirichletOperator_zero_le hcalc F1 P hP hVal1 hDeriv1
  have hTR : ‖fullCoefficientOperatorL hcalc 0 F-fullCoefficientOperatorL hcalc 0 (c • F0)-
      r • fullCoefficientOperatorL hcalc 0 F1‖ ≤ (B*Q)*r^2 := by
    have hEq : fullCoefficientOperatorL hcalc 0 F-fullCoefficientOperatorL hcalc 0 (c • F0)-
        r • fullCoefficientOperatorL hcalc 0 F1 = fullCoefficientOperatorL hcalc 0 R := by
      dsimp only [R]
      simp only [(fullCoefficientOperatorL hcalc 0).map_sub,(fullCoefficientOperatorL hcalc 0).map_smul]
    rw [hEq]
    exact (norm_fullCoefficientOperator_zero_le hcalc R (Q*r^2) hq hValR hDerivR).trans_eq (by ring)
  have hAR : ‖strongDirichletOperator hcalc 0 R‖ ≤ S*(Q*r^2) := norm_strongDirichletOperator_zero_le hcalc R (Q*r^2) hq hValR hDerivR
  have hADiff : ‖strongDirichletOperator hcalc 0 F-strongDirichletOperator hcalc 0 (c • F0)‖ ≤ (S*(Q+P))*r := by
    have hEq : strongDirichletOperator hcalc 0 F-strongDirichletOperator hcalc 0 (c • F0) =
        strongDirichletOperator hcalc 0 R+r • strongDirichletOperator hcalc 0 F1 := by
      have hMap : strongDirichletOperator hcalc 0 R = strongDirichletOperator hcalc 0 F-
          strongDirichletOperator hcalc 0 (c • F0)-r • strongDirichletOperator hcalc 0 F1 := by
        change (strongCoefficientOperatorL hcalc 0) R = (strongCoefficientOperatorL hcalc 0) F-
          (strongCoefficientOperatorL hcalc 0) (c • F0)-r • (strongCoefficientOperatorL hcalc 0) F1
        dsimp only [R]
        simp only [(strongCoefficientOperatorL hcalc 0).map_sub,(strongCoefficientOperatorL hcalc 0).map_smul]
      rw [hMap]
      abel
    rw [hEq]
    calc
      _ ≤ ‖strongDirichletOperator hcalc 0 R‖+‖r • strongDirichletOperator hcalc 0 F1‖ := norm_add_le _ _
      _ = ‖strongDirichletOperator hcalc 0 R‖+r*‖strongDirichletOperator hcalc 0 F1‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
      _ ≤ S*(Q*r^2)+r*(S*P) := add_le_add hAR (mul_le_mul_of_nonneg_left hS1 hr)
      _ ≤ S*(Q*r)+r*(S*P) := by
        gcongr
        nlinarith only [mul_le_mul_of_nonneg_left hr1 hr]
      _ = _ := by ring
  exact ⟨hT1,hADiff,hTR⟩

end ShrinkingSpheres
