module

public import Proof.CalderonN.ActualRelativeWeakEnergyJets
public import Proof.CalderonN.WeakEnergyOperatorFamily
public import Proof.CalderonN.BallRegularity.SmoothCommonSupportStrongOperator

import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
open CalderonN CalderonN.BallDirichlet TauCeti

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency true

namespace CalderonPaper.LowerGreen

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {n : ℕ} [NeZero n]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

variable [FiniteDimensional ℝ P]

theorem contDiff_fixedBallSmoothEnergy_family (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (K : Set (X n)) (hK : IsCompact K) (hK₀ : ∀ p z, z ∉ K → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => fixedBallSmoothEnergyL
      (ha.continuous.comp (continuous_const.prodMk continuous_id) : Continuous (fun z => a (p,z)))) := by
  simp only [commonSupport_fixedBallSmoothEnergy_formula a ha K hK hK₀]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  have hA : ContDiff ℝ ∞ (fun q => a q i j) :=
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.comp ha
  have hSupp (p : P) (z : X n) (hz : z ∉ K) : a (p,z) i j = 0 := by
    rw [hK₀ p z hz]
    rfl
  exact (fixedBallWeakEnergyTermL i j).contDiff.comp
    (contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 0
      (fun q => a q i j) hA K hK hSupp)

theorem contDiffOn_fixedBallWeakInverse_family (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (K : Set (X n)) (hK : IsCompact K) (hK₀ : ∀ p z, z ∉ K → a (p,z) = 0)
    {V : Set P} {lo hi : P → ℝ}
    (hEll : ∀ p ∈ V, PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (fun z => a (p,z)) (lo p) (hi p)) :
    ContDiffOn ℝ ∞ (fun p => (weakEnergyZeroOperatorL (fixedBallZeroInclusionL n)
      (fixedBallSmoothEnergyL (ha.continuous.comp (continuous_const.prodMk continuous_id) :
        Continuous (fun z => a (p,z))))).inverse) V := by
  refine contDiffOn_banachInverseFamily _ V
    (((weakEnergyZeroOperatorL (fixedBallZeroInclusionL n)).contDiff.comp
      (contDiff_fixedBallSmoothEnergy_family a ha K hK hK₀)).contDiffOn) ?_
  intro p hp
  exact weakEnergyZeroOperator_isInvertible _ _
    (isCoercive_fixedBallSmoothEnergy (ha.continuous.comp (continuous_const.prodMk continuous_id)) (hEll p hp))

end CalderonPaper.LowerGreen

end
