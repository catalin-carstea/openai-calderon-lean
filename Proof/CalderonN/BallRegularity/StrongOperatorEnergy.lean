module

public import Proof.CalderonN.BallRegularity.StrongOperatorForcing
public import Proof.CalderonN.BallRegularity.CoordinateFluxEnergy

/-! From Proof/Archive/StrongOperatorEnergy.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


theorem strongCoefficientOperator_energy (hcalc : (FixedSobolevCalculus dim))
    (s : ℕ) (F : (SmoothCoefficientMatrix dim) (s + 2)) (u : (StrongDirichletSpace dim) s)
    (v : (FixedBallH1Zero dim)) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) s
      (strongDirichletOperator hcalc s F u)) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (coefficientMatrixField (s + 2) F) 0 0
        ((strongDirichletProjectionL dim) s u : (FixedBallH1 dim)) (v : (FixedBallH1 dim)) := by
  exact (strongCoefficientOperator_forcing_sum hcalc s F u v).trans
    (energyFormH1_eq_sum_coordinateFlux_inner
      (coefficientMatrixField (s + 2) F)
      ((strongDirichletProjectionL dim) s u : (FixedBallH1 dim)) (v : (FixedBallH1 dim))
      (fun i j => TauCeti.Wkp.value (mu := (volume : Measure (X dim)))
        (Omega := (fixedBallOpens dim)) (p := 2) (s + 1)
          (coefficientMultiplier hcalc (s + 1) (F i j)
            (strongCoordinateDerivativeL hcalc s j u)))
      (fun i j => strongCoefficientFlux_value_ae hcalc s F i j u)).symm


theorem strongCoefficientOperator_energyL0 (hcalc : (FixedSobolevCalculus dim))
    (s : ℕ) (F : (SmoothCoefficientMatrix dim) (s + 2))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F x) 0 0) ⊤
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)))
    (u : (StrongDirichletSpace dim) s) (v : (FixedBallH1Zero dim)) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) hcoeff ((strongDirichletProjectionL dim) s u) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) s
        (strongDirichletOperator hcalc s F u)) v := by
  exact (TauCeti.PDE.energyFormH1L0_apply hcoeff _ _).trans
    (strongCoefficientOperator_energy hcalc s F u v).symm

end CalderonN.BallDirichlet
