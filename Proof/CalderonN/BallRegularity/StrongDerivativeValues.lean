module

public import Proof.CalderonN.BallRegularity.StrongCoefficientOperator
public import Proof.CalderonN.BallRegularity.CoordinateWeakIntegration

/-! From Proof/Archive/StrongDerivativeValues.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


theorem unitBallCoordinateDerivative_eq_coordinateGradient (hcalc : (FixedSobolevCalculus dim))
    (k : ℕ) (i : Fin dim) (u : (BallSobolev dim) (k + 1)) :
    TauCeti.Wkp.value k (unitBallCoordinateDerivativeL hcalc k i u) =
      unitBallCoordinateGradientL i (TauCeti.Wkp.firstOrder k u) := by
  apply Lp.ext
  exact (unitBallCoordinateDerivativeL_value_ae hcalc k i u).trans
    (unitBallCoordinateGradientL_ae i (TauCeti.Wkp.firstOrder k u)).symm

theorem unitBallCoordinateDerivative_inner_integration (hcalc : (FixedSobolevCalculus dim))
    (k : ℕ) (i : Fin dim) (u : (BallSobolev dim) (k + 1)) (v : (FixedBallH1Zero dim)) :
    ⟪TauCeti.Wkp.value k (unitBallCoordinateDerivativeL hcalc k i u),
      TauCeti.W1p.value (v : (FixedBallH1 dim))⟫_ℝ =
      -⟪TauCeti.Wkp.value (k + 1) u, unitBallCoordinateGradientL i (v : (FixedBallH1 dim))⟫_ℝ := by
  rw [unitBallCoordinateDerivative_eq_coordinateGradient]
  exact (unitBall_coordinate_inner_integration (TauCeti.Wkp.firstOrder k u) i v).trans
    (congrArg (fun z => -⟪z, unitBallCoordinateGradientL i (v : (FixedBallH1 dim))⟫_ℝ)
      (TauCeti.Wkp.value_firstOrder k u))

theorem strongCoordinateDerivative_value_ae (hcalc : (FixedSobolevCalculus dim))
    (s : ℕ) (j : Fin dim) (u : (StrongDirichletSpace dim) s) :
    TauCeti.Wkp.value (s + 1) (strongCoordinateDerivativeL hcalc s j u)
      =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
      fun x => (TauCeti.W1p.gradient ((strongDirichletProjectionL dim) s u : (FixedBallH1 dim)) x) j :=
  unitBallCoordinateDerivativeL_value_ae hcalc (s + 1) j (u : (BallSobolev dim) (s + 2))

theorem strongCoefficientFlux_value_ae (hcalc : (FixedSobolevCalculus dim))
    (s : ℕ) (F : (SmoothCoefficientMatrix dim) (s + 2)) (i j : Fin dim)
    (u : (StrongDirichletSpace dim) s) :
    TauCeti.Wkp.value (s + 1) (coefficientMultiplier hcalc (s + 1) (F i j)
      (strongCoordinateDerivativeL hcalc s j u))
      =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
      fun x => coefficientValue (s + 2) (F i j) x *
        (TauCeti.W1p.gradient ((strongDirichletProjectionL dim) s u : (FixedBallH1 dim)) x) j := by
  exact (coefficientMultiplier_value_ae hcalc (s + 1) (F i j)
    (strongCoordinateDerivativeL hcalc s j u)).trans
      (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _)
        (strongCoordinateDerivative_value_ae hcalc s j u))

end CalderonN.BallDirichlet
