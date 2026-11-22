module

public import Proof.CalderonN.FixedBallSourceEnergy
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! From Proof/Archive/StrongDirichletDomain.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]
abbrev BallSobolev (dim : ℕ) (k : ℕ) := TauCeti.Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 k

theorem norm_unitBall_firstOrder_le (k : ℕ) (u : (BallSobolev dim) (k + 1)) :
    ‖TauCeti.Wkp.firstOrder k u‖ ≤ ‖u‖ := by
  induction k with
  | zero => simp only [TauCeti.Wkp.firstOrder_zero]; exact le_rfl
  | succ k ih =>
      rw [TauCeti.Wkp.firstOrder_succ]
      exact (ih _).trans (TauCeti.Wkp.norm_lowerOrder_le (k + 1) u)


def strongDirichletSubmodule (dim : ℕ) (s : ℕ) : ClosedSubmodule ℝ ((BallSobolev dim) (s + 2)) :=
  (TauCeti.w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2).comap
    (TauCeti.Wkp.firstOrderL (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim))
      (p := 2) (s + 1))

theorem mem_strongDirichletSubmodule (s : ℕ) (u : (BallSobolev dim) (s + 2)) :
    u ∈ (strongDirichletSubmodule dim) s ↔
      TauCeti.Wkp.firstOrder (s + 1) u ∈ TauCeti.w1p0Submodule volume (fixedBallOpens dim) 2 :=
  Iff.rfl

abbrev StrongDirichletSpace (dim : ℕ) (s : ℕ) := ↥((strongDirichletSubmodule dim) s)

instance instCompleteSpaceStrongDirichletSpace (s : ℕ) :
    CompleteSpace ((StrongDirichletSpace dim) s) := inferInstance


def strongDirichletProjectionL (dim : ℕ) (s : ℕ) :=
  ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim))
    (p := 2) (s + 1)).comp ((strongDirichletSubmodule dim) s).toSubmodule.subtypeL).codRestrict
      (TauCeti.w1p0Submodule volume (fixedBallOpens dim) 2).toSubmodule
      (fun u => u.2)

theorem strongDirichletProjectionL_apply (s : ℕ) (u : (StrongDirichletSpace dim) s) :
    ((strongDirichletProjectionL dim) s u : (FixedBallH1 dim)) =
      TauCeti.Wkp.firstOrder (s + 1) (u : (BallSobolev dim) (s + 2)) := rfl

theorem strongDirichletProjectionL_injective (s : ℕ) :
    Function.Injective ((strongDirichletProjectionL dim) s) := by
  intro u v h
  apply Subtype.ext
  apply TauCeti.Wkp.ext (s + 2)
  have hfirst := congrArg (fun z : (FixedBallH1Zero dim) => (z : (FixedBallH1 dim))) h
  change TauCeti.Wkp.firstOrder (s + 1) (u : (BallSobolev dim) (s + 2)) =
    TauCeti.Wkp.firstOrder (s + 1) (v : (BallSobolev dim) (s + 2)) at hfirst
  simpa only [TauCeti.Wkp.value_firstOrder] using congrArg TauCeti.W1p.value hfirst

theorem norm_strongDirichletProjectionL_apply_le (s : ℕ) (u : (StrongDirichletSpace dim) s) :
    ‖(strongDirichletProjectionL dim) s u‖ ≤ ‖u‖ :=
  norm_unitBall_firstOrder_le (s + 1) (u : (BallSobolev dim) (s + 2))

end CalderonN.BallDirichlet
