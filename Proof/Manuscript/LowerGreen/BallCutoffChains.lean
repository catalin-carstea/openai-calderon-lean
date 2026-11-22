module

public import Proof.Manuscript.LowerGreen.StrongBallCutoffSteps

import Proof.CalderonN.BallRegularity.SmoothCommonSupportStrongOperator
import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory CalderonN CalderonN.BallDirichlet
open scoped ContDiff ENNReal Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The common supported model for the normalized divergence coefficients
on the fixed unit ball. -/
structure SupportedBallFamily (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (n : ℕ) where
  a : P × X n → Mat n
  smooth : ContDiff ℝ ∞ a
  K : Set (X n)
  compact : IsCompact K
  support : ∀ p z, z ∉ K → a (p,z) = 0
  V : Set P
  openV : IsOpen V
  lo : P → ℝ
  hi : P → ℝ
  elliptic : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n))
    (fun z => a (p,z)) (lo p) (hi p)
  symmetry : ∀ p ∈ V, ∀ z ∈ (fixedBallOpens n : Set (X n)), (a (p,z)).IsSymm

namespace SupportedBallFamily

variable (F : SupportedBallFamily P n)

@[expose] def inverseL (s : ℕ) (p : P) : BallSobolev n s →L[ℝ] BallSobolev n (s+2) :=
  fullStrongBallInverseL s (commonSupportMatrixFamily (s+2) F.a F.smooth F.K F.compact F.support p)

theorem contDiffOn_inverseL (s : ℕ) : ContDiffOn ℝ ∞ (F.inverseL s) F.V := by
  change ContDiffOn ℝ ∞ (fun p => fullStrongBallInverseL s
    (commonSupportMatrixFamily (s+2) F.a F.smooth F.K F.compact F.support p)) F.V
  unfold fullStrongBallInverseL
  exact contDiffOn_const.clm_comp
    (contDiffOn_commonSupport_actual_strongDirichletInverse fixedSobolevCalculus fixedDirichletRegularity
      s F.a F.smooth F.K F.compact F.support F.V F.lo F.hi F.elliptic)

@[expose] def commutatorL (s : ℕ) (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (p : P) :
    BallSobolev n (s+1) →L[ℝ] BallSobolev n s :=
  greenCutoffOperatorFamily s F.a F.smooth χ hχ p

theorem contDiff_commutatorL (s : ℕ) (χ : SmoothData n) (hχ : HasCompactSupport χ.1) :
    ContDiff ℝ ∞ (F.commutatorL s χ hχ) := contDiff_greenCutoffOperatorFamily s F.a F.smooth χ hχ

@[expose] def forwardL (s : ℕ) (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (p : P) :
    BallSobolev n (s+1) →L[ℝ] BallSobolev n (s+2) :=
  (F.inverseL s p).comp (F.commutatorL s χ hχ p)

theorem contDiffOn_forwardL (s : ℕ) (χ : SmoothData n) (hχ : HasCompactSupport χ.1) :
    ContDiffOn ℝ ∞ (F.forwardL s χ hχ) F.V :=
  (F.contDiffOn_inverseL s).clm_comp (F.contDiff_commutatorL s χ hχ).contDiffOn

@[expose] def backwardL (s : ℕ) (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (p : P) :
    BallSobolev n s →L[ℝ] BallSobolev n (s+1) :=
  -((F.commutatorL (s+1) χ hχ p).comp (F.inverseL s p))

theorem contDiffOn_backwardL (s : ℕ) (χ : SmoothData n) (hχ : HasCompactSupport χ.1) :
    ContDiffOn ℝ ∞ (F.backwardL s χ hχ) F.V :=
  ((F.contDiff_commutatorL (s+1) χ hχ).contDiffOn.clm_comp (F.contDiffOn_inverseL s)).neg

variable (χ : ℕ → SmoothData n) (hc : ∀ j, HasCompactSupport (χ j).1)

/-- Compose the first group of cutoffs inward toward the center. -/
@[expose] def forwardChainL (p : P) (j : ℕ) : (m : ℕ) → BallSobolev n 1 →L[ℝ] BallSobolev n (m+1)
  | 0 => ContinuousLinearMap.id ℝ _
  | m+1 => (F.forwardL m (χ j) (hc j) p).comp (forwardChainL p (j+1) m)

theorem contDiffOn_forwardChainL (j m : ℕ) :
    ContDiffOn ℝ ∞ (fun p => F.forwardChainL χ hc p j m) F.V := by
  induction m generalizing j with
  | zero => exact contDiffOn_const
  | succ m ih =>
    exact (F.contDiffOn_forwardL m (χ j) (hc j)).clm_comp (ih (j+1))

/-- Compose the remaining adjoint factors outward. At each step the
initial strong inverse comes before the first-order commutator. -/
@[expose] def backwardChainL (p : P) (j : ℕ) : (m : ℕ) → BallSobolev n 0 →L[ℝ] BallSobolev n m
  | 0 => ContinuousLinearMap.id ℝ _
  | m+1 => (F.backwardL m (χ (j+m)) (hc (j+m)) p).comp (backwardChainL p j m)

theorem contDiffOn_backwardChainL (j m : ℕ) :
    ContDiffOn ℝ ∞ (fun p => F.backwardChainL χ hc p j m) F.V := by
  induction m with
  | zero => exact contDiffOn_const
  | succ m ih =>
    exact (F.contDiffOn_backwardL m (χ (j+m)) (hc (j+m))).clm_comp ih

end SupportedBallFamily

end CalderonPaper.LowerGreen

end
