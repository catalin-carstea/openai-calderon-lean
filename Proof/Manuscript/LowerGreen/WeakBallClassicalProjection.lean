module

public import Proof.Manuscript.LowerGreen.WeakBallInverse
public import Proof.Manuscript.LowerGreen.StrongBallSmoothInverse

import Proof.CalderonN.BallRegularity.StrongOperatorEnergy
import Mathlib.Tactic

public section

noncomputable section

open Set Metric Filter MeasureTheory CalderonN CalderonN.BallDirichlet TauCeti
open scoped ContDiff ENNReal Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

set_option maxHeartbeats 2700000
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency true

private theorem fixedBallWeakInverseL_of_isWeakSolution
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a) (p : P) {lo hi : ℝ}
    (hEll : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (fun z => a (p,z)) lo hi)
    (f : FixedBallL2 n) (w : FixedBallH1Zero n)
    (hSol : PDE.IsWeakSolutionDirichlet (fun z => a (p,z)) 0 0 f w) :
    fixedBallWeakInverseL a ha p
      (PDE.dirichletForcing (mu := (volume : Measure (X n))) (Omega := fixedBallOpens n) f) =
      (w : FixedBallH1 n) := by
  let j := fixedBallZeroInclusionL n
  have hAc : Continuous (fun z => a (p,z)) := ha.continuous.comp (continuous_const.prodMk continuous_id)
  let E := fixedBallSmoothEnergyL hAc
  have hEnergy : weakEnergyZeroOperatorL j E w =
      PDE.dirichletForcing (mu := (volume : Measure (X n))) (Omega := fixedBallOpens n) f := by
    apply ContinuousLinearMap.ext
    intro φ
    rw [weakEnergyZeroOperatorL_apply]
    exact (fixedBallSmoothEnergyL_apply hAc (j w) (j φ)).trans (hSol φ)
  have hInv := weakEnergyZeroOperator_isInvertible j E
    (isCoercive_fixedBallSmoothEnergy hAc hEll)
  change j ((weakEnergyZeroOperatorL j E).inverse _) = j w
  exact congrArg j ((congrArg (weakEnergyZeroOperatorL j E).inverse hEnergy.symm).trans
    (hInv.inverse_apply_self w))

private theorem strongL0_projection_isWeakSolution (A : SmoothCoefficientMatrix n 2) {lo hi : ℝ}
    (hEll : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n))
      (coefficientMatrixField 2 A) lo hi)
    (f : BallSobolev n 0) :
    PDE.IsWeakSolutionDirichlet (coefficientMatrixField 2 A) 0 0 (Wkp.value 0 f)
      (strongDirichletProjectionL n 0 ((strongDirichletOperator fixedSobolevCalculus 0 A).inverse f)) := by
  let L := strongDirichletOperator fixedSobolevCalculus 0 A
  let v := L.inverse f
  have hL := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 A hEll
  intro φ
  have h := strongCoefficientOperator_energy fixedSobolevCalculus 0 A v φ
  rw [show strongDirichletOperator fixedSobolevCalculus 0 A v = f from hL.self_apply_inverse _] at h
  exact h.symm

/-- The weak inverse agrees with the smooth solution when tested on a
global smooth forcing and a smooth zero-boundary solution of the same equation. -/
theorem fixedBallWeakInverseL_of_classical
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (K : Set (X n)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (p : P) {lo hi : ℝ}
    (hEll : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (fun z => a (p,z)) lo hi)
    (f w : SmoothData n) (hw : EqOn w.1 0 (standardSphere n))
    (hEq : EqOn (negativeBallDivergence (fun z => a (p,z)) w.1) f.1 (ball (0 : X n) 1)) :
    fixedBallWeakInverseL a ha p
      (PDE.dirichletForcing (mu := (volume : Measure (X n))) (Omega := fixedBallOpens n)
        (Wkp.value 0 (smoothBallSobolev 0 f))) =
      smoothBallSobolev 1 w := by
  let A := commonSupportMatrixFamily 2 a ha K hK hSupp p
  have hA : coefficientMatrixField 2 A = fun z => a (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily _ a ha K hK hSupp p
  have hEllA : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n))
      (coefficientMatrixField 2 A) lo hi := hA ▸ hEll
  let v := (strongDirichletOperator fixedSobolevCalculus 0 A).inverse (smoothBallSobolev 0 f)
  let w₀ := strongDirichletProjectionL n 0 v
  have hv : v.1 = smoothBallSobolev 2 w :=
    fullStrongBallInverseL_of_classical a ha K hK hSupp p hEll f w hw hEq 0
  have hVal : (w₀ : FixedBallH1 n) = smoothBallSobolev 1 w := by
    rw [show (w₀ : FixedBallH1 n) = Wkp.firstOrder 1 v.1 from strongDirichletProjectionL_apply 0 v,
      hv]
    exact (firstOrder_smoothBallSobolev 1 w).trans (firstOrder_smoothBallSobolev 0 w).symm
  have hWeak := strongL0_projection_isWeakSolution A hEllA (smoothBallSobolev 0 f)
  rw [hA] at hWeak
  exact (fixedBallWeakInverseL_of_isWeakSolution a ha p hEll _ w₀ hWeak).trans hVal

end CalderonPaper.LowerGreen

end
