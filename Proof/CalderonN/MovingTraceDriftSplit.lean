module

public import Proof.CalderonN.PhysicalMovingTraceDecomposition

import Mathlib.Tactic

/-! Retain the drift acting on the leading angular velocity in the
lower-order term. The remaining drift is estimated directly in norm. -/

public section

set_option autoImplicit false
namespace CalderonN

variable {R ι : Type*} [Ring R] [Fintype ι]

@[expose] def movingTraceDriftRemainder (b D E F : ι → R) : R :=
  ∑ i,b i*(D i+(E i+F i))

theorem movingTracePerturbation_split_drift (a h : ι → ι → R) (b V D E F : ι → R) :
    movingTracePerturbation a h b V D E F =
      movingTracePerturbation a h 0 V D E F+movingTraceDriftRemainder b D E F := by
  classical
  unfold movingTracePerturbation movingTraceDriftRemainder
  dsimp only
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,Pi.add_apply]

end CalderonN
