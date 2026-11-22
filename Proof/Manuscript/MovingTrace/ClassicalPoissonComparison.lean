module

public import Proof.Manuscript.MovingTrace.FixedBallTrialCorrection
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2800000

open CalderonN CalderonN.BallDirichlet Set Metric
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
local notation "Z" => X dim

/-- A Dirichlet trial minus a strong zero-trace correction has the same
boundary jets as the canonical harmonic extension. -/
theorem fixedBallPoisson_eq_trial_sub_residual
    {U : Set Z} (hU : IsOpen U) (hCU : closedBall (0 : Z) 1 ⊆ U)
    (g a : MetricField dim) (hG : SmoothMetric U g) (ha : ContDiff ℝ ∞ a)
    (hA : ∀ z ∈ U, ∀ i j, a z i j = divergenceCoeff g z i j)
    (u b d f : Z → ℝ) (hu : ContDiff ℝ ∞ u) (hb : ContDiff ℝ ∞ b)
    (hDatum : EqOn u d (standardSphere dim)) (hB : EqOn b 0 (standardSphere dim))
    (hEu : EqOn (negativeBallDivergence a u) f (ball (0 : Z) 1))
    (hEb : EqOn (negativeBallDivergence a b) f (ball (0 : Z) 1)) :
    ContDiff ℝ ∞ (fixedBallPoisson g d) ∧
      ∀ l : ℕ, ∀ z ∈ closedBall (0 : Z) 1,
        iteratedFDeriv ℝ l (fixedBallPoisson g d) z =
          iteratedFDeriv ℝ l u z - iteratedFDeriv ℝ l b z := by
  let sol : Z → ℝ := u - b
  have hSolD : ContDiff ℝ ∞ sol := hu.sub hb
  have hLap (z : Z) (hz : z ∈ ball (0 : Z) 1) : laplace g sol z = 0 := by
    have hzU := hCU (ball_subset_closedBall hz)
    have hD := negativeBallDivergence_eq_neg_laplace hU hG hA hSolD.contDiffOn hzU
    have hD₀ := negativeBallDivergence_sub_solution ha ⟨u,hu⟩ ⟨b,hb⟩ z
    change negativeBallDivergence a sol z = negativeBallDivergence a u z -
      negativeBallDivergence a b z at hD₀
    rw [hEu hz,hEb hz,sub_self] at hD₀
    rw [hD₀] at hD
    exact (mul_eq_zero.mp (neg_eq_zero.mp hD.symm)).resolve_left
      (Real.sqrt_pos.mpr (hG.2 z hzU).det_pos).ne'
  have hSol : FixedBallSolution g d sol := by
    refine ⟨hSolD,fun z hz => ?_,hLap⟩
    change u z - b z = d z
    rw [show b z = 0 from hB hz,sub_zero]
    exact hDatum hz
  have hExist : ∃ w, FixedBallSolution g d w := ⟨sol,hSol⟩
  have hCan : FixedBallSolution g d (fixedBallPoisson g d) := by
    unfold fixedBallPoisson
    rw [dite_eq_left hExist]
    exact Classical.choose_spec hExist
  have hCmp := eqOn_fixedBallSolution hU hCU hG hCan hSol (fun _ _ => rfl)
  refine ⟨hCan.1,fun l z hz => ?_⟩
  rw [eqOn_iteratedFDeriv_closedUnitBall hCan.1 hSolD hCmp l hz]
  exact fun_iteratedFDeriv_sub_apply (hu.contDiffAt.of_le (by simp))
    (hb.contDiffAt.of_le (by simp))

end CalderonPaper
