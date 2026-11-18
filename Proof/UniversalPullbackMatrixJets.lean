import Proof.CompactFiniteJetBound
import Proof.NormalFrameCoefficientModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

abbrev PullbackMatrixInput := Mat × ((X →L[ℝ] X) × (X →L[ℝ] X))

def universalPullbackMetricMatrix (q : PullbackMatrixInput) : Mat :=
  fun i j => ∑ a,∑ b,q.1 a b*(q.2.1 (q.2.2 (axis i))) a*(q.2.1 (q.2.2 (axis j))) b

lemma contDiff_universalPullbackMetricMatrix : ContDiff ℝ ∞ universalPullbackMetricMatrix := by
  have hA : ContDiff ℝ ∞ (fun q : PullbackMatrixInput => q.1) := contDiff_fst
  have hJ : ContDiff ℝ ∞ (fun q : PullbackMatrixInput => q.2.1) := contDiff_snd.fst
  have hL : ContDiff ℝ ∞ (fun q : PullbackMatrixInput => q.2.2) := contDiff_snd.snd
  have hSlot (i : I) : ContDiff ℝ ∞ (fun q : PullbackMatrixInput => q.2.1 (q.2.2 (axis i))) :=
    hJ.clm_apply (hL.clm_apply contDiff_const)
  have hEntry (i a : I) : ContDiff ℝ ∞ (fun q : PullbackMatrixInput => (q.2.1 (q.2.2 (axis i))) a) :=
    (EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.comp (hSlot i)
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
    (((contDiff_pi.mp (contDiff_pi.mp hA a) b).mul (hEntry i a)).mul (hEntry j b))))

lemma normalFrameMetric_eq_universal_pullback (g : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) :
    normalFrameMetric g E q = universalPullbackMetricMatrix
      (g (E (normalFrameInput q)),
        (normalVerticalJacobian E (normalFrameInput q).1 (normalFrameInput q).2,q.1.2.2)) := by
  ext i j
  rfl

theorem exists_universalPullbackMetricMatrix_jet_bound (A J L : ℝ) (N : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ n : ℕ,n ≤ N → ∀ q : PullbackMatrixInput,
      ‖q.1‖ ≤ A → ‖q.2.1‖ ≤ J → ‖q.2.2‖ ≤ L →
      ‖iteratedFDeriv ℝ n universalPullbackMetricMatrix q‖ ≤ C := by
  let K : Set PullbackMatrixInput := Metric.closedBall (0:Mat) A ×ˢ
    (Metric.closedBall (0:X →L[ℝ] X) J ×ˢ Metric.closedBall (0:X →L[ℝ] X) L)
  have hK : IsCompact K := (isCompact_closedBall (0:Mat) A).prod
    ((isCompact_closedBall (0:X →L[ℝ] X) J).prod (isCompact_closedBall (0:X →L[ℝ] X) L))
  obtain ⟨C,hC,hBound⟩ := exists_finite_jet_bound_on_compact universalPullbackMetricMatrix K hK
    (fun _ _ => contDiff_universalPullbackMetricMatrix.contDiffAt) N
  refine ⟨C,hC,?_⟩
  intro n hn q hA hJ hL
  apply hBound n hn q
  simpa only [K,mem_prod,Metric.mem_closedBall,dist_zero_right] using And.intro hA (And.intro hJ hL)

end ShrinkingSpheres
