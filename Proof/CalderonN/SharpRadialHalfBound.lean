module

public import Proof.CalderonN.ActualFiniteRadialEndpoints

import Mathlib.Tactic

/-! State the native radial trace estimate directly as an operator
bound on a smooth fixed-ball representative. -/

public section

noncomputable section
set_option autoImplicit false
namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_smoothBallRadialDerivative_half_le (hn : 3 ≤ dim) (u : SmoothData dim) :
    ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (smoothBallRadialDerivative u)‖ ≤
      Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))*‖smoothBallSobolev 2 u‖ := by
  have hArea : 0 < unitSphereArea dim := unitSphereArea_pos
  let C := ((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  apply sq_smoothBoundarySobolev_half_of_truncations hn
  intro k
  apply le_of_mul_le_mul_left _ hArea
  refine (sum_sharpBallRadialTrace_le u k).trans_eq ?_
  change C*‖smoothBallSobolev 2 u‖^2 = unitSphereArea dim*(Real.sqrt (C/unitSphereArea dim)*‖smoothBallSobolev 2 u‖)^2
  rw [mul_pow,Real.sq_sqrt (div_nonneg hC hArea.le),← mul_assoc,mul_comm (unitSphereArea dim) _,
    div_mul_cancel₀ _ hArea.ne']

end CalderonN
