module

public import Proof.Manuscript.LowerGreen.BallCenterEvaluation
public import Proof.CalderonN.SmoothClosedRangeLift

import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory CalderonN CalderonN.BallDirichlet
open scoped ContDiff InnerProductSpace

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n]

theorem maps_closedBallSobolev_of_smooth {s t : ℕ}
    (A : BallSobolev n s →L[ℝ] BallSobolev n t)
    (h : ∀ f : SmoothData n, ∃ g : SmoothData n, A (smoothBallSobolev s f) = smoothBallSobolev t g)
    (x : ClosedBallSobolev n s) : A x.1 ∈ closedBallSobolev n t := by
  refine (denseRange_denseSmoothBallSobolev n s).induction_on x ?_ ?_
  · exact (closedBallSobolev n t).isClosed.preimage (A.continuous.comp continuous_subtype_val)
  · intro f
    obtain ⟨g,hg⟩ := h ⟨f.1,f.2⟩
    change A (smoothBallSobolev s ⟨f.1,f.2⟩) ∈ closedBallSobolev n t
    rw [hg]
    exact (denseSmoothBallSobolev n t ⟨g.1,g.2⟩).2

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem exists_smooth_closedBall_lift {V : Set P} (hV : IsOpen V) {s : ℕ}
    {A : P → BallSobolev n s} (hA : ContDiffOn ℝ ∞ A V) (hMem : ∀ p ∈ V, A p ∈ closedBallSobolev n s) :
    ∃ B : P → ClosedBallSobolev n s, ContDiffOn ℝ ∞ B V ∧ ∀ p ∈ V, (B p).1 = A p := by
  classical
  let B (p : P) : ClosedBallSobolev n s := if hp : p ∈ V then ⟨A p,hMem p hp⟩ else 0
  let J : ClosedBallSobolev n s →ₗᵢ[ℝ] BallSobolev n s := (closedBallSobolev n s).toSubmodule.subtypeₗᵢ
  have hEq (p : P) (hp : p ∈ V) : (B p).1 = A p := by simp [B,hp]
  refine ⟨B,?_,hEq⟩
  apply contDiffOn_top_of_closedRangeLinearIsometry hV J B
  exact hA.congr hEq

/-- Riesz representative on the closed smooth subspace of volume L².
This preserves membership in the closed jet model at every later order. -/
@[expose] def closedBallCenterRiesz (s : ℕ) (A : BallSobolev n s →L[ℝ] ℝ)
    (T : BallSobolev n 0 →L[ℝ] BallSobolev n s) : ClosedBallSobolev n 0 :=
  (InnerProductSpace.toDual ℝ (ClosedBallSobolev n 0)).symm
    ((A.comp T).comp (closedBallSobolev n 0).toSubmodule.subtypeL)

theorem closedBallCenterRiesz_inner (s : ℕ) (A : BallSobolev n s →L[ℝ] ℝ)
    (T : BallSobolev n 0 →L[ℝ] BallSobolev n s) (f : ClosedBallSobolev n 0) :
    ⟪(closedBallCenterRiesz s A T).1, f.1⟫_ℝ = A (T f.1) := by
  change ⟪closedBallCenterRiesz s A T, f⟫_ℝ = _
  rw [← InnerProductSpace.toDual_apply_apply,closedBallCenterRiesz,LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem contDiffOn_closedBallCenterRiesz
    {s : ℕ} (A : BallSobolev n s →L[ℝ] ℝ)
    {T : P → BallSobolev n 0 →L[ℝ] BallSobolev n s} {V : Set P} (hT : ContDiffOn ℝ ∞ T V) :
    ContDiffOn ℝ ∞ (fun p => closedBallCenterRiesz s A (T p)) V :=
  (InnerProductSpace.toDual ℝ (ClosedBallSobolev n 0)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    ((contDiffOn_const.clm_comp hT).clm_comp contDiffOn_const)

end CalderonPaper.LowerGreen

end
