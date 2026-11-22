module

public import Proof.CalderonN.BallRegularity.StrongOperatorForcing

/-! From Proof/Archive/CoefficientMatrixRegularity.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


theorem contDiff_coefficientMatrixField (r : ℕ) (F : (SmoothCoefficientMatrix dim) r) :
    ContDiff ℝ ∞ (coefficientMatrixField r F) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_coefficientValue r (F i j)

theorem contDiffOn_coefficientMatrixField_closedBall (r : ℕ)
    (F : (SmoothCoefficientMatrix dim) r) :
    ContDiffOn ℝ ∞ (coefficientMatrixField r F) (Metric.closedBall 0 2) :=
  (contDiff_coefficientMatrixField r F).contDiffOn

theorem aestronglyMeasurable_coefficientMatrixField (r : ℕ)
    (F : (SmoothCoefficientMatrix dim) r) :
    AEStronglyMeasurable (coefficientMatrixField r F)
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
  (contDiff_coefficientMatrixField r F).continuous.aestronglyMeasurable

theorem memLp_coefficientMatrixEnergyIntegrand (r : ℕ) (F : (SmoothCoefficientMatrix dim) r)
    {lam Lam : ℝ} (ha : TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (coefficientMatrixField r F) lam Lam) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField r F x) 0 0) ⊤
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
  TauCeti.PDE.memLp_energyIntegrand_of_bounds ha.upper_nonneg
    (aestronglyMeasurable_coefficientMatrixField r F)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx eta xi => ha.upper_bound hx eta xi)
    (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)

end CalderonN.BallDirichlet
