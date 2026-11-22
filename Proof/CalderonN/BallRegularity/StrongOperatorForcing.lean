module

public import Proof.CalderonN.BallRegularity.StrongDerivativeValues
public import Proof.CalderonN.BallRegularity.StrongOperatorTyped

/-! From Proof/Archive/StrongOperatorForcing.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


def coefficientMatrixField (r : ℕ) (F : (SmoothCoefficientMatrix dim) r) :
    (X dim) → Matrix (Fin dim) (Fin dim) ℝ :=
  fun x i j => coefficientValue r (F i j) x

theorem strongCoefficientOperator_forcing_sum (hcalc : (FixedSobolevCalculus dim))
    (s : ℕ) (F : (SmoothCoefficientMatrix dim) (s + 2)) (u : (StrongDirichletSpace dim) s)
    (v : (FixedBallH1Zero dim)) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) s
      (strongDirichletOperator hcalc s F u)) v =
      ∑ i : Fin dim, ∑ j : Fin dim,
        ⟪TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) (s + 1) (coefficientMultiplier hcalc (s + 1) (F i j)
          (strongCoordinateDerivativeL hcalc s j u)),
          unitBallCoordinateGradientL i (v : (FixedBallH1 dim))⟫_ℝ := by
  rw [TauCeti.PDE.dirichletForcing_apply, strongDirichletOperator_apply]
  change ⟪TauCeti.Wkp.valueL s (-∑ i, ∑ j,
    unitBallCoordinateDerivativeL hcalc s i (coefficientMultiplier hcalc (s + 1) (F i j)
      (strongCoordinateDerivativeL hcalc s j u))), TauCeti.W1p.value (v : (FixedBallH1 dim))⟫_ℝ = _
  simp only [map_neg, map_sum, inner_neg_left, sum_inner, TauCeti.Wkp.valueL_apply]
  simp_rw [unitBallCoordinateDerivative_inner_integration hcalc s]
  simp only [Finset.sum_neg_distrib, neg_neg]

end CalderonN.BallDirichlet
