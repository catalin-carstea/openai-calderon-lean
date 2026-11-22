module

public import Proof.CalderonN.BallRegularity.DivergenceOperatorFamily

/-! From Proof/Archive/SobolevDivergenceAssembly.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


 
def unitBallCoordinateDerivativeL (hcalc : (FixedSobolevCalculus dim)) (k : ℕ) (i : Fin dim) :=
  Classical.choose (hcalc.2 k i)

theorem unitBallCoordinateDerivativeL_value_ae (hcalc : (FixedSobolevCalculus dim))
    (k : ℕ) (i : Fin dim) (u : (BallSobolev dim) (k + 1)) :
    TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) k
      (unitBallCoordinateDerivativeL hcalc k i u)
      =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
      fun x => (TauCeti.W1p.gradient (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim))
        (p := 2) (TauCeti.Wkp.firstOrder k u) x) i :=
  Classical.choose_spec (hcalc.2 k i) u

 
def unitBallDivergenceL (hcalc : (FixedSobolevCalculus dim)) (s : ℕ) :=
  coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
    (fun j => (unitBallCoordinateDerivativeL hcalc (s + 1) j).comp
      ((strongDirichletSubmodule dim) s).toSubmodule.subtypeL)

end CalderonN.BallDirichlet
