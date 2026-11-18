import Proof.CompactFiniteJetBound
import Proof.NormalFrameNormalizationDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.MetricOperator
open OAI.AnisotropicCalderon.NormalCoordinatesFrame

abbrev MatrixFrameInput := Mat × (X →L[ℝ] X)

def universalFrameGram (q : MatrixFrameInput) : X →L[ℝ] X :=
  q.2.adjoint.comp ((matrixOperatorMap q.1.transpose).comp q.2)

def universalMatrixFrameNormalizer (q : MatrixFrameInput) : X →L[ℝ] X :=
  q.2.comp (frameOperator (metricGramFrame (universalFrameGram q)))

lemma contDiff_universalFrameGram : ContDiff ℝ ∞ universalFrameGram := by
  have hA : ContDiff ℝ ∞ (fun q : MatrixFrameInput => q.1) := contDiff_fst
  have hL : ContDiff ℝ ∞ (fun q : MatrixFrameInput => q.2) := contDiff_snd
  have hTranspose : ContDiff ℝ ∞ (fun q : MatrixFrameInput => q.1.transpose) :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => contDiff_pi.mp (contDiff_pi.mp hA j) i))
  have hAdj := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X)).contDiff.comp hL
  exact hAdj.clm_comp ((matrixOperatorMap.contDiff.comp hTranspose).clm_comp hL)

lemma contDiffAt_universalMatrixFrameNormalizer_of_gram_id (q : MatrixFrameInput)
    (hq : universalFrameGram q = ContinuousLinearMap.id ℝ X) :
    ContDiffAt ℝ ∞ universalMatrixFrameNormalizer q := by
  have hPos : ∀ u : X,u ≠ 0 → 0 < OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair (universalFrameGram q) u u := by
    intro u hu
    rw [OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair,hq,ContinuousLinearMap.id_apply]
    exact real_inner_self_pos.mpr hu
  exact contDiffAt_snd.clm_comp (contDiffAt_metricGramFrameOperator universalFrameGram q
    contDiff_universalFrameGram.contDiffAt hPos)

lemma normalFrameNormalizedLinear_eq_universal (g : MetricField) (p : NormalFrameParameter) :
    normalFrameNormalizedLinear g p = universalMatrixFrameNormalizer (g p.1,p.2.2) := rfl

/-- This compact set concerns a fixed universal algebraic normalization,
not an arbitrary admitted metric family. Its jet bounds may therefore be
used uniformly over all admitted metrics satisfying the displayed budgets. -/
def universalOrthonormalFrameSet (A0 L0 : ℝ) : Set MatrixFrameInput :=
  {q | ‖q.1‖ ≤ A0 ∧ ‖q.2‖ ≤ L0 ∧ universalFrameGram q = ContinuousLinearMap.id ℝ X}

lemma isCompact_universalOrthonormalFrameSet (A0 L0 : ℝ) :
    IsCompact (universalOrthonormalFrameSet A0 L0) := by
  have hClosed : IsClosed {q : MatrixFrameInput | universalFrameGram q = ContinuousLinearMap.id ℝ X} :=
    isClosed_eq contDiff_universalFrameGram.continuous continuous_const
  have he : universalOrthonormalFrameSet A0 L0 =
      (Metric.closedBall (0:Mat) A0 ×ˢ Metric.closedBall (0:X →L[ℝ] X) L0) ∩
        {q : MatrixFrameInput | universalFrameGram q = ContinuousLinearMap.id ℝ X} := by
    ext q
    simp only [universalOrthonormalFrameSet,mem_ofPred_eq,mem_inter_iff,mem_prod,
      Metric.mem_closedBall,dist_zero_right]
    tauto
  rw [he]
  exact ((isCompact_closedBall (0:Mat) A0).prod (isCompact_closedBall (0:X →L[ℝ] X) L0)).inter_right hClosed

/-- Every finite jet of the universal normalization has a common bound
on the bounded orthonormal locus. The constant depends only on the two
size bounds and the requested finite order. -/
theorem exists_universalMatrixFrameNormalizer_jet_bound (A0 L0 : ℝ) (N : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ n : ℕ,n ≤ N → ∀ q ∈ universalOrthonormalFrameSet A0 L0,
      ‖iteratedFDeriv ℝ n universalMatrixFrameNormalizer q‖ ≤ C := by
  apply exists_finite_jet_bound_on_compact universalMatrixFrameNormalizer
    (universalOrthonormalFrameSet A0 L0) (isCompact_universalOrthonormalFrameSet A0 L0) _ N
  intro q hq
  exact contDiffAt_universalMatrixFrameNormalizer_of_gram_id q hq.2.2

end ShrinkingSpheres
