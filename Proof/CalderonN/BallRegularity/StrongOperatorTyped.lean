module

public import Proof.CalderonN.BallRegularity.StrongCoefficientOperator

/-! From Proof/Archive/StrongOperatorTyped.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


def strongDirichletOperator (hcalc : (FixedSobolevCalculus dim)) (s : ℕ)
    (F : (SmoothCoefficientMatrix dim) (s + 2)) : (StrongDirichletSpace dim) s →L[ℝ] (BallSobolev dim) s :=
  strongCoefficientOperatorL hcalc s F

theorem strongDirichletOperator_eq (hcalc : (FixedSobolevCalculus dim)) (s : ℕ)
    (F : (SmoothCoefficientMatrix dim) (s + 2)) :
    strongDirichletOperator hcalc s F = strongCoefficientOperatorL hcalc s F := rfl

theorem strongDirichletOperator_apply (hcalc : (FixedSobolevCalculus dim)) (s : ℕ)
    (F : (SmoothCoefficientMatrix dim) (s + 2)) (u : (StrongDirichletSpace dim) s) :
    strongDirichletOperator hcalc s F u =
      -∑ i, ∑ j, unitBallCoordinateDerivativeL hcalc s i
        (coefficientMultiplier hcalc (s + 1) (F i j)
          (strongCoordinateDerivativeL hcalc s j u)) :=
  strongCoefficientOperatorL_apply_apply hcalc s F u

end CalderonN.BallDirichlet
