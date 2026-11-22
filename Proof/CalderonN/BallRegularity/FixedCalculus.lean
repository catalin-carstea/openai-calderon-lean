module

public import Proof.CalderonN.BallRegularity.Spaces
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! From Proof/Archive/(FixedSobolevCalculus dim).lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Function
open scoped ENNReal ContDiff
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]
def FixedSobolevCalculus (dim : ℕ) : Prop :=
  (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ phi : (X dim) → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
    ∀ M : ℝ, 0 ≤ M →
    (∀ j : ℕ, j ≤ k + 1 → ∀ x : (X dim), ‖iteratedFDeriv ℝ j phi x‖ ≤ M) →
    ∃ T : (BallSobolev dim) k →L[ℝ] (BallSobolev dim) k,
      (∀ f : (BallSobolev dim) k,
        TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) k (T f)
          =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
          fun x => phi x * TauCeti.Wkp.value (mu := (volume : Measure (X dim)))
            (Omega := (fixedBallOpens dim)) (p := 2) k f x) ∧ ‖T‖ ≤ C * M) ∧
  (∀ (k : ℕ) (i : Fin dim), ∃ D : (BallSobolev dim) (k + 1) →L[ℝ] (BallSobolev dim) k,
    ∀ u : (BallSobolev dim) (k + 1),
      TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) k (D u)
        =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
        fun x => (TauCeti.W1p.gradient (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim))
          (p := 2) (TauCeti.Wkp.firstOrder k u) x) i)

end CalderonN.BallDirichlet
