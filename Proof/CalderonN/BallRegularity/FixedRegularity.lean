module

public import Proof.CalderonN.BallRegularity.Spaces

/-! From Proof/Archive/(FixedDirichletRegularity dim).lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxSynthPendingDepth 10

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]
def FixedDirichletRegularity (dim : ℕ) : Prop :=
  ∀ (s : ℕ) (a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ) (lam Lam : ℝ),
    ContDiffOn ℝ ∞ a (Metric.closedBall 0 2) →
    TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim)) a lam Lam →
    ∀ (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure (X dim)).restrict (fixedBallOpens dim))),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (BallSobolev dim) s) (u : (FixedBallH1Zero dim)),
      (∀ v : (FixedBallH1Zero dim), TauCeti.PDE.energyFormH1L0 hcoeff u v =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim))
          (TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) s f) v) →
      ∃ U : (BallSobolev dim) (s + 2),
        TauCeti.Wkp.firstOrder (s + 1) U = (u : (FixedBallH1 dim)) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖)


end CalderonN.BallDirichlet
