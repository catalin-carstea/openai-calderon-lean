import Proof.CompactFiniteJetBound
import Proof.NormalFrameCoefficientModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

abbrev NormalizedMatrixCoefficientInput := (ℝ × ℝ) × Mat

/-- The normalized first divergence coefficient is a fixed function of
    the two positive central diagonal entries and the pullback metric. -/
def universalNormalizedMatrixCoefficient (q : NormalizedMatrixCoefficientInput) : Mat :=
  fun i j => Real.exp ((1/2:ℝ)*(Real.log q.1.1-Real.log q.1.2))*
    (Real.sqrt q.2.det*q.2⁻¹ i j)

lemma contDiffAt_universalNormalizedMatrixCoefficient (q : NormalizedMatrixCoefficientInput)
    (ha : 0 < q.1.1) (hb : 0 < q.1.2) (hDet : 0 < q.2.det) :
    ContDiffAt ℝ ∞ universalNormalizedMatrixCoefficient q := by
  have hA : ContDiffAt ℝ ∞ (fun r : NormalizedMatrixCoefficientInput => r.1.1) q := contDiffAt_fst.fst
  have hB : ContDiffAt ℝ ∞ (fun r : NormalizedMatrixCoefficientInput => r.1.2) q := contDiffAt_fst.snd
  have hExp : ContDiffAt ℝ ∞ (fun r : NormalizedMatrixCoefficientInput =>
      Real.exp ((1/2:ℝ)*(Real.log r.1.1-Real.log r.1.2))) q :=
    (contDiffAt_const.mul ((hA.log ha.ne').sub (hB.log hb.ne'))).exp
  have hMatrix : ContDiffAt ℝ ∞ (fun r : NormalizedMatrixCoefficientInput => r.2) q := contDiffAt_snd
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact hExp.mul (contDiffAt_matrix_density_inverse_entry
    (fun r : NormalizedMatrixCoefficientInput => r.2) q
    (fun a b => contDiffAt_pi.mp (contDiffAt_pi.mp hMatrix a) b) hDet i j)

lemma normalFrameNormalizedCoefficient_eq_universal (g g₁ : MetricField)
    (E : X × X → X) (q : NormalFrameParameter × X) :
    normalFrameNormalizedCoefficient g g₁ E q = universalNormalizedMatrixCoefficient
      ((g q.1.1 0 0,g₁ q.1.1 0 0),normalFrameMetric g₁ E q) := by
  have hInv : (firstMetricDensityFactor g g₁ q.1.1)⁻¹ =
      Real.exp ((1/2:ℝ)*(Real.log (g q.1.1 0 0)-Real.log (g₁ q.1.1 0 0))) := by
    rw [firstMetricDensityFactor,Real.exp_neg,inv_inv]
    rfl
  ext i j
  simp only [normalFrameNormalizedCoefficient,universalNormalizedMatrixCoefficient,
    matrixFamilyCoefficient,matrixFamilyDensity,hInv]

def universalNormalizedMatrixCoefficientSet (lo hi A delta : ℝ) : Set NormalizedMatrixCoefficientInput :=
  {q | q.1.1 ∈ Icc lo hi ∧ q.1.2 ∈ Icc lo hi ∧ ‖q.2‖ ≤ A ∧ delta ≤ q.2.det}

lemma isCompact_universalNormalizedMatrixCoefficientSet (lo hi A delta : ℝ) :
    IsCompact (universalNormalizedMatrixCoefficientSet lo hi A delta) := by
  have hClosed : IsClosed {q : NormalizedMatrixCoefficientInput | delta ≤ q.2.det} :=
    isClosed_le continuous_const continuous_snd.matrix_det
  have he : universalNormalizedMatrixCoefficientSet lo hi A delta =
      ((Icc lo hi ×ˢ Icc lo hi) ×ˢ Metric.closedBall (0:Mat) A) ∩
        {q : NormalizedMatrixCoefficientInput | delta ≤ q.2.det} := by
    ext q
    simp only [universalNormalizedMatrixCoefficientSet,mem_ofPred_eq,mem_inter_iff,mem_prod,
      Metric.mem_closedBall,dist_zero_right]
    tauto
  rw [he]
  exact ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall (0:Mat) A)).inter_right hClosed

theorem exists_universalNormalizedMatrixCoefficient_jet_bound (lo hi A delta : ℝ)
    (hLo : 0 < lo) (hDelta : 0 < delta) (N : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ n : ℕ,n ≤ N →
      ∀ q ∈ universalNormalizedMatrixCoefficientSet lo hi A delta,
        ‖iteratedFDeriv ℝ n universalNormalizedMatrixCoefficient q‖ ≤ C := by
  apply exists_finite_jet_bound_on_compact universalNormalizedMatrixCoefficient
    (universalNormalizedMatrixCoefficientSet lo hi A delta)
    (isCompact_universalNormalizedMatrixCoefficientSet lo hi A delta) _ N
  intro q hq
  exact contDiffAt_universalNormalizedMatrixCoefficient q (hLo.trans_le hq.1.1)
    (hLo.trans_le hq.2.1.1) (hDelta.trans_le hq.2.2.2)

end ShrinkingSpheres
