module

public import Proof.Manuscript.LowerGreen.WeakBallEnergyInverse
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

@[expose] def fixedBallWeakInverseL
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a) (p : P) :
    (FixedBallH1Zero n →L[ℝ] ℝ) →L[ℝ] FixedBallH1 n :=
  (fixedBallZeroInclusionL n).comp
    (weakEnergyZeroOperatorL (fixedBallZeroInclusionL n)
      (fixedBallSmoothEnergyL (ha.continuous.comp (continuous_const.prodMk continuous_id) :
        Continuous (fun z => a (p,z))))).inverse

private theorem contDiffOn_postcomp_weak
    {D Z H : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : Z →L[ℝ] H) {A : P → D →L[ℝ] Z} {V : Set P} (hA : ContDiffOn ℝ ∞ A V) :
    ContDiffOn ℝ ∞ (fun p => j.comp (A p)) V := contDiffOn_const.clm_comp hA

theorem contDiffOn_fixedBallWeakInverseL
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (K : Set (X n)) (hK : IsCompact K) (hK₀ : ∀ p z, z ∉ K → a (p,z) = 0)
    {V : Set P} {lo hi : P → ℝ}
    (hEll : ∀ p ∈ V, PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (fun z => a (p,z)) (lo p) (hi p)) :
    ContDiffOn ℝ ∞ (fixedBallWeakInverseL a ha) V := by
  let L (p : P) : (FixedBallH1Zero n →L[ℝ] ℝ) →L[ℝ] FixedBallH1Zero n :=
    (weakEnergyZeroOperatorL (fixedBallZeroInclusionL n)
      (fixedBallSmoothEnergyL (ha.continuous.comp (continuous_const.prodMk continuous_id) :
        Continuous (fun z => a (p,z))))).inverse
  have hL : ContDiffOn ℝ ∞ L V := contDiffOn_fixedBallWeakInverse_family a ha K hK hK₀ hEll
  exact contDiffOn_postcomp_weak (fixedBallZeroInclusionL n) hL


end CalderonPaper.LowerGreen

end
