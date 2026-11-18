import Proof.FlatFullCoefficientOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Coefficient multipliers depend only on the coefficient inside the ball. -/
theorem coefficientMultiplier_congr_on_ball (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F G : SmoothCoefficientJets (k+1))
    (hEq : ∀ x ∈ (ballOpens : Set X),coefficientValue (k+1) F x = coefficientValue (k+1) G x) :
    coefficientMultiplier hcalc k F = coefficientMultiplier hcalc k G := by
  apply ContinuousLinearMap.ext
  intro U
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F U,
    coefficientMultiplier_value_ae hcalc k G U,
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx hy hball
  rw [hx,hy,hEq x hball]

/-- The strong inverse is independent of the compact coefficient extension. -/
theorem strongDirichletOperator_congr_on_ball (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F G : SmoothCoefficientMatrix (s+2))
    (hEq : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField (s+2) F x = coefficientMatrixField (s+2) G x) :
    strongDirichletOperator hcalc s F = strongDirichletOperator hcalc s G := by
  apply ContinuousLinearMap.ext
  intro U
  rw [strongDirichletOperator_apply,strongDirichletOperator_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficientMultiplier_congr_on_ball hcalc (s+1) (F i j) (G i j)
    (fun x hx => congrArg (fun A : Mat => A i j) (hEq x hx))]

/-- The full H2-to-L2 operator has the same locality property. -/
theorem fullCoefficientOperator_congr_on_ball (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F G : SmoothCoefficientMatrix (s+2))
    (hEq : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField (s+2) F x = coefficientMatrixField (s+2) G x) :
    fullCoefficientOperatorL hcalc s F = fullCoefficientOperatorL hcalc s G := by
  apply ContinuousLinearMap.ext
  intro U
  rw [fullCoefficientOperatorL_apply_apply,fullCoefficientOperatorL_apply_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficientMultiplier_congr_on_ball hcalc (s+1) (F i j) (G i j)
    (fun x hx => congrArg (fun A : Mat => A i j) (hEq x hx))]

end ShrinkingSpheres
