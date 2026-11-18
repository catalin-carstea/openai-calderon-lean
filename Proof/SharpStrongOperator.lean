import Proof.SharpCoefficientMultiplier
import Proof.Archive.StrongOperatorTyped

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

def strongC1OperatorBudget (hcalc : FixedSobolevCalculus) : ℝ :=
  2*‖unitBallDivergenceL hcalc 0‖

lemma strongC1OperatorBudget_nonneg (hcalc : FixedSobolevCalculus) : 0 ≤ strongC1OperatorBudget hcalc := by
  unfold strongC1OperatorBudget
  positivity

/-- Local C0 and C1 control suffices for the H2-to-L2 strong operator bound. -/
theorem norm_strongDirichletOperator_zero_le (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
    ‖strongDirichletOperator hcalc 0 F‖ ≤ strongC1OperatorBudget hcalc*q := by
  have hMatrix : ‖coefficientMatrixMultiplierL hcalc 0 F‖ ≤ 2*q := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*q)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*q)).2
    intro j
    change ‖coefficientMultiplier hcalc 1 (F i j)‖ ≤ 2*q
    exact norm_coefficientMultiplier_one_le hcalc (F i j) q hq (hValue i j) (hDerivative i j)
  change ‖unitBallDivergenceL hcalc 0 (coefficientMatrixMultiplierL hcalc 0 F)‖ ≤ _
  exact ((unitBallDivergenceL hcalc 0).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hMatrix (norm_nonneg _)).trans_eq
      (by unfold strongC1OperatorBudget; ring))

/-- The same local estimate controls perturbations of the actual strong operator. -/
theorem norm_strongDirichletOperator_zero_sub_le (hcalc : FixedSobolevCalculus)
    (F F0 : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-F0) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-F0) i j)) x‖ ≤ q) :
    ‖strongDirichletOperator hcalc 0 F-strongDirichletOperator hcalc 0 F0‖ ≤ strongC1OperatorBudget hcalc*q := by
  have hEq : strongDirichletOperator hcalc 0 F-strongDirichletOperator hcalc 0 F0 =
      strongDirichletOperator hcalc 0 (F-F0) := (map_sub (strongCoefficientOperatorL hcalc 0) F F0).symm
  rw [hEq]
  exact norm_strongDirichletOperator_zero_le hcalc (F-F0) q hq hValue hDerivative

end ShrinkingSpheres
