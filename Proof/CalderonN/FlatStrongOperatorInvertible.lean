module

public import Proof.CalderonN.BallRegularity.UniformStrongInverse

import Mathlib.Tactic

/-! The flat strong Dirichlet operator uses only the coefficient
on the fixed open ball. -/

public section

noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

theorem flatStrongOperator_isInvertible (s : ℕ) (F₀ : SmoothCoefficientMatrix dim (s+2))
    (hFlat : ∀ z ∈ closedBall (0:X dim) 2, coefficientMatrixField (s+2) F₀ z = 1) :
    (strongDirichletOperator (fixedSobolevCalculus (dim:=dim)) s F₀).IsInvertible := by
  have h : TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (fun _ => (1:Mat dim)) 1 1 :=
    TauCeti.PDE.uniformlyEllipticOn_const_one_one (n:=Fin dim) ((fixedBallOpens dim) : Set (X dim))
  have hEq : EqOn (coefficientMatrixField (s+2) F₀) (fun _ : X dim => (1:Mat dim)) (fixedBallOpens dim) := by
    intro z hz
    have hz' : dist z (0:X dim) < 1 := hz
    exact (hFlat z (mem_closedBall.mpr (hz'.le.trans (by norm_num))))
  exact strongDirichletOperator_isInvertible_of_elliptic
    (fixedSobolevCalculus (dim:=dim)) (fixedDirichletRegularity (dim:=dim)) s F₀ (h.congr hEq)

end CalderonN.BallDirichlet
