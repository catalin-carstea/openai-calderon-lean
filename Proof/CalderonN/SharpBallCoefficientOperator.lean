module

public import Proof.CalderonN.BallPoissonOperator

import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Multiplication
import Mathlib.Tactic

/-! The local C¹ multiplier and fixed-ball estimates from
`SharpCoefficientMultiplier`, `SharpStrongOperator`, and
`FullCoefficientEnergy` in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`.
The full-ball operator uses the same fixed Sobolev calculus as the Poisson
solver. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim]

/-- The existing coefficient multiplier on H1 needs only the coefficient and
    its first derivative on the ball; its ambient second jet does not enter. -/
theorem norm_coefficientMultiplier_one_le (hcalc : FixedSobolevCalculus dim)
    (F : SmoothCoefficientJets dim 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ x ∈ ((fixedBallOpens dim) : Set (X dim)),|coefficientValue 2 F x| ≤ q)
    (hDerivative : ∀ x ∈ ((fixedBallOpens dim) : Set (X dim)),‖fderiv ℝ (coefficientValue 2 F) x‖ ≤ q) :
    ‖coefficientMultiplier hcalc 1 F‖ ≤ 2*q := by
  have hSmooth := contDiff_coefficientValue 2 F
  have hGrad (x : X dim) (hx : x ∈ ((fixedBallOpens dim) : Set (X dim))) : ‖gradient (coefficientValue 2 F) x‖ ≤ q := by
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hDerivative x hx
  let T : BallSobolev dim 1 →L[ℝ] BallSobolev dim 1 := TauCeti.W1p.contDiffSMulL
    (mu:=(volume : Measure (X dim))) (Omega:=(fixedBallOpens dim)) (p:=2)
    (coefficientValue 2 F) hSmooth hq hValue hGrad
  have hEq : coefficientMultiplier hcalc 1 F = T := by
    apply ContinuousLinearMap.ext
    intro u
    apply TauCeti.W1p.ext_value
    apply Lp.ext
    have h1 : TauCeti.W1p.value (coefficientMultiplier hcalc 1 F u) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
        fun x => coefficientValue 2 F x*TauCeti.W1p.value u x := by
      simpa only [TauCeti.Wkp.value_one] using coefficientMultiplier_value_ae hcalc 1 F u
    have h2 : TauCeti.W1p.value (T u) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
        fun x => coefficientValue 2 F x*TauCeti.W1p.value u x := by
      change TauCeti.W1p.value
        (TauCeti.W1p.contDiffSMul (coefficientValue 2 F) hSmooth hq hValue hGrad u) =ᵐ[_] _
      have hh := TauCeti.W1p.value_contDiffSMul_ae (mu:=(volume : Measure (X dim)))
        (Omega:=(fixedBallOpens dim)) (p:=2) (psi:=coefficientValue 2 F) hSmooth hq hValue hGrad u
      filter_upwards [hh] with x hx
      simpa only [smul_eq_mul] using hx
    exact h1.trans h2.symm
  rw [hEq]
  exact TauCeti.W1p.norm_contDiffSMulL_le hSmooth hq hValue hGrad

@[expose] def strongC1OperatorBudget (hcalc : FixedSobolevCalculus dim) : ℝ :=
  2*‖unitBallDivergenceL hcalc 0‖

lemma strongC1OperatorBudget_nonneg (hcalc : FixedSobolevCalculus dim) : 0 ≤ strongC1OperatorBudget hcalc := by
  unfold strongC1OperatorBudget
  positivity

/-- Local C0 and C1 control suffices for the H2-to-L2 strong operator bound. -/
theorem norm_strongDirichletOperator_zero_le (hcalc : FixedSobolevCalculus dim)
    (F : SmoothCoefficientMatrix dim 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ ((fixedBallOpens dim) : Set (X dim)),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ ((fixedBallOpens dim) : Set (X dim)),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
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
theorem norm_strongDirichletOperator_zero_sub_le (hcalc : FixedSobolevCalculus dim)
    (F F0 : SmoothCoefficientMatrix dim 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ ((fixedBallOpens dim) : Set (X dim)),|coefficientValue 2 ((F-F0) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ ((fixedBallOpens dim) : Set (X dim)),‖fderiv ℝ (coefficientValue 2 ((F-F0) i j)) x‖ ≤ q) :
    ‖strongDirichletOperator hcalc 0 F-strongDirichletOperator hcalc 0 F0‖ ≤ strongC1OperatorBudget hcalc*q := by
  have hEq : strongDirichletOperator hcalc 0 F-strongDirichletOperator hcalc 0 F0 =
      strongDirichletOperator hcalc 0 (F-F0) := (map_sub (strongCoefficientOperatorL hcalc 0) F F0).symm
  rw [hEq]
  exact norm_strongDirichletOperator_zero_le hcalc (F-F0) q hq hValue hDerivative

@[expose] def fullC1OperatorBudget  : ℝ :=
  2*‖coefficientDivergenceL (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 0)
    (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 1)‖

lemma fullC1OperatorBudget_nonneg  : 0 ≤ fullC1OperatorBudget (dim := dim) := by
  unfold fullC1OperatorBudget
  positivity

/-- Local C0/C1 coefficients control the full H2-to-L2 divergence operator. -/
theorem norm_fullCoefficientOperator_zero_le 
    (F : SmoothCoefficientMatrix dim 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ ((fixedBallOpens dim) : Set (X dim)),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ ((fixedBallOpens dim) : Set (X dim)),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
    ‖fullBallDivergenceL 0 F‖ ≤ fullC1OperatorBudget (dim := dim)*q := by
  have hMatrix : ‖coefficientMatrixMultiplierL (fixedSobolevCalculus (dim := dim)) 0 F‖ ≤ 2*q := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*q)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*q)).2
    intro j
    exact norm_coefficientMultiplier_one_le (fixedSobolevCalculus (dim := dim)) (F i j) q hq (hValue i j) (hDerivative i j)
  change ‖coefficientDivergenceL (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 0)
    (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 1) (coefficientMatrixMultiplierL (fixedSobolevCalculus (dim := dim)) 0 F)‖ ≤ _
  exact ((coefficientDivergenceL (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 0)
    (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 1)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hMatrix (norm_nonneg _)).trans_eq
      (by unfold fullC1OperatorBudget;ring))

end CalderonN
