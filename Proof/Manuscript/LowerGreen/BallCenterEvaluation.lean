module

public import Proof.CalderonN.ClosedBallJetEvaluation
public import Mathlib.Analysis.InnerProductSpace.Dual

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic

public section

open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace
open CalderonN CalderonN.BallDirichlet

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n]

noncomputable section

/-- The bounded point evaluation obtained from the closed-ball Sobolev
embedding, restricted to the center. -/
def closedBallCenterEvalL (s : ℕ) : ClosedBallSobolev n s →L[ℝ] ℝ :=
  let center : UnitClosedBall n := ⟨0, by simp⟩
  let evalJet := (ContinuousMap.evalCLM ℝ center).comp (closedBallJetL n 0 s)
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => X n) ℝ (fun _ => 0)).comp evalJet

theorem closedBallCenterEvalL_smooth {s : ℕ} (h : n+1 ≤ s) (f : smoothBallDataSubmodule n) :
    closedBallCenterEvalL s (denseSmoothBallSobolev n s f) = f.1 0 := by
  unfold closedBallCenterEvalL
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [closedBallJetL_on_smooth 0 s (by simpa using h)]
  rfl

/-- A fixed bounded extension is available on the full native space.
Only its values on smooth data enter the subsequent identities. -/
theorem exists_ballCenterEvalL {s : ℕ} (h : n+1 ≤ s) :
    ∃ A : BallSobolev n s →L[ℝ] ℝ,
      ∀ f : smoothBallDataSubmodule n, A (smoothBallSobolevLinear n s f) = f.1 0 := by
  obtain ⟨A,hA,_⟩ := exists_extension_norm_eq ((closedBallSobolev n s).toSubmodule)
    (closedBallCenterEvalL s)
  refine ⟨A, fun f => ?_⟩
  have hz := hA (denseSmoothBallSobolev n s f)
  exact hz.trans (closedBallCenterEvalL_smooth h f)

end

end CalderonPaper.LowerGreen
