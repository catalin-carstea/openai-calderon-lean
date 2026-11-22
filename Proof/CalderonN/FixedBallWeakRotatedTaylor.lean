module

public import Proof.CalderonN.FixedBallWeakConormalFamilyJets
public import Proof.CalderonN.WeakConormalRotatedTaylorJets

import Mathlib.Tactic

/-! Quadratic joint Taylor bounds for the weak form of the genuine
conormal rotation commutator. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def fixedBallWeakRotatedSolution (r : ℝ)
    (E₁ E₂ : FixedBallEnergyOperator dim) :
    SphereSobolev dim (1/2:ℝ) →L[ℝ] FixedBallH1 dim := by
  let E : FixedBallEnergyOperator dim := fixedBallFlatEnergyL dim+r • E₁+r^2 • E₂
  exact weakEnergyPoissonOperatorL (fixedBallZeroInclusionL dim) E (harmonicFirstOrderLift dim)

@[expose] def fixedBallWeakRotatedCompose (r : ℝ) (T₁ T₂ : FixedBallEnergyOperator dim)
    (U : SphereSobolev dim (1/2:ℝ) →L[ℝ] FixedBallH1 dim) :
    SphereSobolev dim (1/2:ℝ) →L[ℝ] SphereSobolev dim (1/2:ℝ) →L[ℝ] ℝ := by
  let T : FixedBallEnergyOperator dim := r • T₁+r^2 • T₂
  exact T.bilinearComp U U

@[expose] def fixedBallWeakRotatedSubtract (r : ℝ) (T₁ : FixedBallEnergyOperator dim)
    (B : SphereSobolev dim (1/2:ℝ) →L[ℝ] SphereSobolev dim (1/2:ℝ) →L[ℝ] ℝ) :
    SphereSobolev dim (1/2:ℝ) →L[ℝ] SphereSobolev dim (1/2:ℝ) →L[ℝ] ℝ := by
  let A : SphereSobolev dim (1/2:ℝ) →L[ℝ] SphereSobolev dim (1/2:ℝ) →L[ℝ] ℝ :=
    T₁.bilinearComp (harmonicFirstOrderLift dim) (harmonicFirstOrderLift dim)
  exact B-r • A

@[expose] def fixedBallWeakConormalRotatedTaylor (r : ℝ)
    (E₁ E₂ T₁ T₂ : FixedBallEnergyOperator dim) :
    SphereSobolev dim (1/2:ℝ) →L[ℝ] SphereSobolev dim (1/2:ℝ) →L[ℝ] ℝ :=
  fixedBallWeakRotatedSubtract r T₁
    (fixedBallWeakRotatedCompose r T₁ T₂ (fixedBallWeakRotatedSolution r E₁ E₂))

end CalderonN
