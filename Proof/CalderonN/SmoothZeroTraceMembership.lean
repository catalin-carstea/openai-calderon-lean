module

public import Proof.CalderonN.SmoothStrongBallEstimates

import Mathlib.Tactic

/-! A smooth function vanishing on the sphere has the same native
representative as the strong zero-Dirichlet inverse of its own forcing. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothSobolev_mem_zero_of_eqOn_sphere
    (F : SmoothCoefficientMatrix dim 2) {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi)
    (u : SmoothData dim) (hu : EqOn u.1 0 (standardSphere dim)) :
    smoothSobolev u ∈ w1p0Submodule volume (fixedBallOpens dim) 2 := by
  let A := coefficientMatrixField 2 F
  have hA : ContDiff ℝ ∞ A := contDiff_coefficientMatrixField 2 F
  let g : SmoothData dim := ⟨negativeBallDivergence A u.1,contDiff_negativeBallDivergence hA u.2⟩
  obtain ⟨w,hwT,hwE,hwRep⟩ := exists_native_classical_zeroDirichlet F hEll g
  have hEq : EqOn u.1 w.1 (closedBall (0 : X dim) 1) :=
    eqOn_closedUnitBall_of_equal_ball_forcing hA hEll (fun _ _ => rfl) u w
      (fun z hz => (hwE hz).symm) (hu.trans hwT.symm)
  let z := (strongDirichletOperator fixedSobolevCalculus 0 F).inverse (smoothBallSobolev 0 g)
  have hMem := (mem_strongDirichletSubmodule 0 (z : BallSobolev dim 2)).mp z.property
  have hRep : smoothBallSobolev 2 w = (z : BallSobolev dim 2) := hwRep
  rw [← firstOrder_smoothBallSobolev 1 u,
    smoothBallSobolev_eq_of_eqOn_ball 2 u w (hEq.mono ball_subset_closedBall),hRep]
  exact hMem

end CalderonN
