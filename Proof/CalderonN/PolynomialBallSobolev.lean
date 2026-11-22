module

public import Proof.CalderonN.ClosedBallJetEvaluation
public import Proof.CalderonN.SmoothAngularCasimir

import Mathlib.Tactic

public section

noncomputable section
open MvPolynomial
open scoped ContDiff

namespace CalderonN

open OAI.AnisotropicCalderon.GreenRadialTrace BallDirichlet

variable {dim : ℕ} [NeZero dim]

@[expose] def polynomialSmoothDataL : MvPolynomial (Fin dim) ℝ →ₗ[ℝ] smoothBallDataSubmodule dim where
  toFun := fun p => ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
  map_add' := by
    intro p q
    apply Subtype.ext
    funext z
    exact map_add (eval (euclideanCoordinates dim z)) p q
  map_smul' := by
    intro c p
    apply Subtype.ext
    funext z
    change eval (euclideanCoordinates dim z) (c • p) = c * eval (euclideanCoordinates dim z) p
    rw [smul_eq_C_mul,map_mul,eval_C]

def polynomialBallSobolevL (k : ℕ) :
    MvPolynomial (Fin dim) ℝ →ₗ[ℝ] BallSobolev dim k :=
  (smoothBallSobolevLinear dim k).comp polynomialSmoothDataL

theorem polynomialBallSobolevL_apply (k : ℕ) (p : MvPolynomial (Fin dim) ℝ) :
    polynomialBallSobolevL k p =
      smoothBallSobolev k ⟨polynomialEvaluation p, contDiff_polynomialEvaluation p⟩ := by
  unfold polynomialBallSobolevL polynomialSmoothDataL
  rfl

/-- The smooth solid polynomial represented in the native first-order
unit-ball Sobolev space. -/
def polynomialBallH1L (dim : ℕ) [NeZero dim] :
    MvPolynomial (Fin dim) ℝ →ₗ[ℝ] FixedBallH1 dim :=
  (TauCeti.Wkp.firstOrderL 0).toLinearMap.comp (polynomialBallSobolevL 1)

theorem polynomialBallH1L_apply (p : MvPolynomial (Fin dim) ℝ) :
    polynomialBallH1L dim p =
      smoothSobolev ⟨polynomialEvaluation p, contDiff_polynomialEvaluation p⟩ := by
  change TauCeti.Wkp.firstOrderL 0 (polynomialBallSobolevL 1 p) = _
  rw [polynomialBallSobolevL_apply]
  exact firstOrder_smoothBallSobolev 0 _

end CalderonN
