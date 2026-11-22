module

public import Proof.CalderonN.WeakConormalUniformJets
public import Proof.CalderonN.ActualRelativeWeakEnergyGerm

import Proof.CalderonN.HarmonicH1Lift
import Mathlib.Tactic

/-! Specialize the weak conormal Taylor estimate to the harmonic lift
of the unit ball, including the two flat-energy cancellations. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency true
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim]

theorem fixedBallFlatWeakEnergy_isInvertible (dim : ℕ) [NeZero dim] :
    (weakEnergyZeroOperatorL (fixedBallZeroInclusionL dim) (fixedBallFlatEnergyL dim)).IsInvertible := by
  apply weakEnergyZeroOperator_isInvertible
  exact isCoercive_fixedBallSmoothEnergy continuous_const
    (uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim)))

@[expose] def fixedBallWeakConormalFamily (E : FixedBallEnergyOperator dim) :=
  let P₀ := harmonicFirstOrderLift dim
  E.bilinearComp (weakEnergyPoissonOperatorL (fixedBallZeroInclusionL dim) E P₀) P₀

@[expose] def fixedBallWeakConormalAffine (E : FixedBallEnergyOperator dim) :=
  let P₀ := harmonicFirstOrderLift dim
  E.bilinearComp P₀ P₀

@[expose] def fixedBallWeakConormalTaylor (r : ℝ) (E₁ E₂ : FixedBallEnergyOperator dim) :=
  let E₀ := fixedBallFlatEnergyL dim
  fixedBallWeakConormalFamily (E₀+r • E₁+r^2 • E₂)-fixedBallWeakConormalAffine E₀-
    r • fixedBallWeakConormalAffine E₁

variable [Nontrivial (Fin dim)]

theorem exists_fixedBall_weakConormal_family_jet_budget
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (N : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) δ, ∀ x : P,
      ∀ E₁ E₂ : P → FixedBallEnergyOperator dim,
      LocalSmoothJetBudget E₁ x N D → LocalSmoothJetBudget E₂ x N D →
      (∀ᶠ p in 𝓝 x,(weakEnergyZeroOperatorL (fixedBallZeroInclusionL dim)
        (fixedBallFlatEnergyL dim+r • E₁ p+r^2 • E₂ p)).IsInvertible) ∧
      LocalSmoothJetBudget (fun p => fixedBallWeakConormalTaylor r (E₁ p) (E₂ p)) x N (C*r^2) := by
  exact exists_weakConormal_taylor_jet_budget (P:=P) (fixedBallZeroInclusionL dim)
    (fixedBallFlatEnergyL dim) (harmonicFirstOrderLift dim) (fixedBallFlatWeakEnergy_isInvertible dim)
    fixedBallFlatEnergyL_harmonicFirstOrderLift_zero
    (fun u v => fixedBallFlatEnergyL_harmonicFirstOrderLift_zero_left v u) N D hD

end CalderonN
