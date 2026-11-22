module

public import Proof.CalderonN.SharpBallValueTrace
public import Proof.CalderonN.BallRadialDerivative

import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

public section

noncomputable section
open scoped ContDiff
set_option maxHeartbeats 1550000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The actual outward derivative has the sharp order-one mapping
from bulk (H^2) to boundary (H^{1/2}). The weights use the harmonic
projections in the angular coercivity model. -/
theorem sum_sharpBallRadialTrace_le (u : SmoothData dim) (s : Finset ℕ) :
    let v := smoothBallRadialDerivative u
    unitSphereArea dim * ∑ k ∈ s, (1+(k : ℝ)) *
      ‖harmonicProjection k (smoothSphereLift v.1 v.2)‖^2 ≤
      ((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2*‖smoothBallSobolev 2 u‖^2 := by
  let v := smoothBallRadialDerivative u
  have h := sum_sharpBallValueTrace_le v s
  have hs : smoothSobolev v = TauCeti.Wkp.firstOrder 0 (ballRadialDerivativeL dim (smoothBallSobolev 2 u)) := by
    rw [ballRadialDerivativeL_smooth]
    exact (firstOrder_smoothBallSobolev 0 v).symm
  have hb : ‖smoothSobolev v‖ ≤ ‖ballRadialDerivativeL dim‖ * ‖smoothBallSobolev 2 u‖ := by
    rw [hs]
    exact (norm_unitBall_firstOrder_le 0 _).trans ((ballRadialDerivativeL dim).le_opNorm _)
  have hq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
  exact (h.trans (mul_le_mul_of_nonneg_left hq (by positivity))).trans_eq (by ring)

theorem summable_sharpBallRadialTrace (u : SmoothData dim) :
    let v := smoothBallRadialDerivative u
    let f (k : ℕ) := (1+(k : ℝ)) * ‖harmonicProjection k (smoothSphereLift v.1 v.2)‖^2
    Summable f ∧ (∑' k, f k) ≤
      ((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2*‖smoothBallSobolev 2 u‖^2 /
        unitSphereArea dim := by
  let v := smoothBallRadialDerivative u
  let f (k : ℕ) := (1+(k : ℝ)) * ‖harmonicProjection k (smoothSphereLift v.1 v.2)‖^2
  have hn : ∀ k, 0 ≤ f k := by intro k; dsimp [f]; positivity
  have h (s : Finset ℕ) :
      ∑ k ∈ s, f k ≤ ((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2*‖smoothBallSobolev 2 u‖^2 /
        unitSphereArea dim :=
    (le_div_iff₀ unitSphereArea_pos).mpr (by simpa only [mul_comm] using sum_sharpBallRadialTrace_le u s)
  exact ⟨summable_of_sum_le hn h,Real.tsum_le_of_sum_le hn h⟩

end CalderonN
