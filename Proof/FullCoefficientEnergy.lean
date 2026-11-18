import Proof.Archive.FullSobolevCoefficientOperator
import Proof.Archive.StrongOperatorEnergy
import Proof.SharpCoefficientMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- The generic full Sobolev operator has the same weak energy identity as its
    zero-boundary restriction; no boundary condition on U is needed. -/
theorem fullCoefficientOperator_energy (hcalc : FixedSobolevCalculus)
    (s : ℕ) (F : SmoothCoefficientMatrix (s+2)) (U : BallSobolev (s+2))
    (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (TauCeti.Wkp.value (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) s
        (fullCoefficientOperatorL hcalc s F U)) v =
      TauCeti.PDE.energyFormH1 (coefficientMatrixField (s+2) F) 0 0
        (TauCeti.Wkp.firstOrder (s+1) U) (v : BallH1) := by
  have hForcing : TauCeti.PDE.dirichletForcing (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (TauCeti.Wkp.value (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) s
        (fullCoefficientOperatorL hcalc s F U)) v =
      ∑ i : Fin 3,∑ j : Fin 3,
        ⟪TauCeti.Wkp.value (s+1) (coefficientMultiplier hcalc (s+1) (F i j)
          (unitBallCoordinateDerivativeL hcalc (s+1) j U)),
          unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ := by
    rw [TauCeti.PDE.dirichletForcing_apply,fullCoefficientOperatorL_apply_apply]
    change ⟪TauCeti.Wkp.valueL s (-∑ i,∑ j,
      unitBallCoordinateDerivativeL hcalc s i (coefficientMultiplier hcalc (s+1) (F i j)
        (unitBallCoordinateDerivativeL hcalc (s+1) j U))),TauCeti.W1p.value (v : BallH1)⟫_ℝ = _
    simp only [map_neg,map_sum,inner_neg_left,sum_inner,TauCeti.Wkp.valueL_apply]
    simp_rw [unitBallCoordinateDerivative_inner_integration hcalc s]
    simp only [Finset.sum_neg_distrib,neg_neg]
  exact hForcing.trans (energyFormH1_eq_sum_coordinateFlux_inner
    (coefficientMatrixField (s+2) F) (TauCeti.Wkp.firstOrder (s+1) U) (v : BallH1)
    (fun i j => TauCeti.Wkp.value (s+1) (coefficientMultiplier hcalc (s+1) (F i j)
      (unitBallCoordinateDerivativeL hcalc (s+1) j U))) (fun i j =>
        (coefficientMultiplier_value_ae hcalc (s+1) (F i j)
          (unitBallCoordinateDerivativeL hcalc (s+1) j U)).trans
          (EventuallyEq.mul (EventuallyEq.refl _ _)
            (unitBallCoordinateDerivativeL_value_ae hcalc (s+1) j U)))).symm

def fullC1OperatorBudget (hcalc : FixedSobolevCalculus) : ℝ :=
  2*‖coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)‖

lemma fullC1OperatorBudget_nonneg (hcalc : FixedSobolevCalculus) : 0 ≤ fullC1OperatorBudget hcalc := by
  unfold fullC1OperatorBudget
  positivity

/-- Local C0/C1 coefficients control the full H2-to-L2 divergence operator. -/
theorem norm_fullCoefficientOperator_zero_le (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
    ‖fullCoefficientOperatorL hcalc 0 F‖ ≤ fullC1OperatorBudget hcalc*q := by
  have hMatrix : ‖coefficientMatrixMultiplierL hcalc 0 F‖ ≤ 2*q := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*q)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*q)).2
    intro j
    exact norm_coefficientMultiplier_one_le hcalc (F i j) q hq (hValue i j) (hDerivative i j)
  change ‖coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1) (coefficientMatrixMultiplierL hcalc 0 F)‖ ≤ _
  exact ((coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hMatrix (norm_nonneg _)).trans_eq
      (by unfold fullC1OperatorBudget;ring))

end ShrinkingSpheres
