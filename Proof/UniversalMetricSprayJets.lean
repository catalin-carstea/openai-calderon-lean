import Proof.CompactFiniteJetBound
import Proof.MatrixFamilyCalculus
import Proof.MatrixFieldHigherJetNorms
import Proof.NormalGeodesicPhase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

abbrev MetricConnectionInput := Mat × (X →L[ℝ] Mat)
abbrev MetricSprayInput := Mat × ((X →L[ℝ] Mat) × X)

def universalChristoffel (q : MetricConnectionInput) (k i j : I) : ℝ :=
  (∑ l, q.1⁻¹ k l*((q.2 (axis i)) l j+(q.2 (axis j)) i l-(q.2 (axis l)) i j))/2

def universalMetricConnection (q : MetricConnectionInput) : X →L[ℝ] X →L[ℝ] X :=
  ∑ i,∑ j,∑ k,universalChristoffel q k i j • coordinateBilinearAtom i j k

def universalMetricSpray (q : MetricSprayInput) : X × X :=
  (q.2.2,-universalMetricConnection (q.1,q.2.1) q.2.2 q.2.2)

lemma contDiffAt_universalChristoffel (q : MetricConnectionInput)
    (hDet : q.1.det ≠ 0) (k i j : I) :
    ContDiffAt ℝ ∞ (fun r => universalChristoffel r k i j) q := by
  let U : Set MetricConnectionInput := {r | r.1.det ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage continuous_fst.matrix_det
  have hA (a b : I) : ContDiffOn ℝ ∞ (fun r : MetricConnectionInput => r.1 a b) U :=
    (contDiff_pi.mp (contDiff_pi.mp contDiff_fst a) b).contDiffOn
  have hInv (a b : I) : ContDiffAt ℝ ∞ (fun r : MetricConnectionInput => r.1⁻¹ a b) q :=
    (contDiffOn_matrixFamily_inverse_entry (S:=U) (fun r : MetricConnectionInput => r.1) hA (fun r hr => hr) a b).contDiffAt
      (hU.mem_nhds hDet)
  have hD (a b c : I) : ContDiffAt ℝ ∞ (fun r : MetricConnectionInput => (r.2 (axis a)) b c) q :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_snd.clm_apply contDiffAt_const) b) c
  exact (ContDiffAt.sum (fun l _ => (hInv k l).mul (((hD i l j).add (hD j i l)).sub (hD l i j)))).div_const 2

lemma contDiffAt_universalMetricConnection (q : MetricConnectionInput) (hDet : q.1.det ≠ 0) :
    ContDiffAt ℝ ∞ universalMetricConnection q := by
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => ContDiffAt.sum
    (fun k _ => (contDiffAt_universalChristoffel q hDet k i j).smul contDiffAt_const)))

lemma contDiffAt_universalMetricSpray (q : MetricSprayInput) (hDet : q.1.det ≠ 0) :
    ContDiffAt ℝ ∞ universalMetricSpray q := by
  have hC := (contDiffAt_universalMetricConnection (q.1,q.2.1) hDet).comp q
    (contDiffAt_fst.prodMk contDiffAt_snd.fst)
  exact contDiffAt_snd.snd.prodMk ((hC.clm_apply contDiffAt_snd.snd).clm_apply contDiffAt_snd.snd).neg

lemma universalMetricConnection_actual (g : MetricField) (x : X) (hg : ContDiffAt ℝ ∞ g x) :
    universalMetricConnection (g x,fderiv ℝ g x) = connectionBilinear g x := by
  have hEntry (i j : I) : DifferentiableAt ℝ (fun y => g y i j) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).differentiableAt (by simp)
  have hD := (hasFDerivAt_matrixFamily_of_entries g x hEntry).fderiv
  have hΓ (k i j : I) : universalChristoffel (g x,fderiv ℝ g x) k i j = christoffel g x k i j := by
    simp only [universalChristoffel,christoffel,coordDeriv,hD,matrixFamilyDerivative_apply_entry]
  simp only [universalMetricConnection,hΓ,connectionBilinear,coordinateBilinearAtom]

lemma universalMetricSpray_actual (g : MetricField) (x v : X) (hg : ContDiffAt ℝ ∞ g x) :
    universalMetricSpray (g x,(fderiv ℝ g x,v)) = coordinateGeodesicSpray g (x,v) := by
  rw [universalMetricSpray,universalMetricConnection_actual g x hg,connectionBilinear_apply]
  rfl

/-- A compact finite-dimensional locus for a single universal rational map.
    The determinant floor is explicit; no compactness of admitted metric
    fields or their normal-coordinate maps is asserted. -/
def universalMetricSpraySet (A D V delta : ℝ) : Set MetricSprayInput :=
  {q | ‖q.1‖ ≤ A ∧ ‖q.2.1‖ ≤ D ∧ ‖q.2.2‖ ≤ V ∧ delta ≤ |q.1.det|}

lemma isCompact_universalMetricSpraySet (A D V delta : ℝ) :
    IsCompact (universalMetricSpraySet A D V delta) := by
  have hClosed : IsClosed {q : MetricSprayInput | delta ≤ |q.1.det|} :=
    isClosed_le continuous_const continuous_fst.matrix_det.abs
  have he : universalMetricSpraySet A D V delta =
      (Metric.closedBall (0:Mat) A ×ˢ (Metric.closedBall (0:X →L[ℝ] Mat) D ×ˢ Metric.closedBall (0:X) V)) ∩
        {q : MetricSprayInput | delta ≤ |q.1.det|} := by
    ext q
    simp only [universalMetricSpraySet,mem_ofPred_eq,mem_inter_iff,mem_prod,
      Metric.mem_closedBall,dist_zero_right]
    tauto
  rw [he]
  exact ((isCompact_closedBall (0:Mat) A).prod
    ((isCompact_closedBall (0:X →L[ℝ] Mat) D).prod (isCompact_closedBall (0:X) V))).inter_right hClosed

theorem exists_universalMetricSpray_jet_bound (A D V delta : ℝ) (hDelta : 0 < delta) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, n ≤ N → ∀ q ∈ universalMetricSpraySet A D V delta,
      ‖iteratedFDeriv ℝ n universalMetricSpray q‖ ≤ C := by
  apply exists_finite_jet_bound_on_compact universalMetricSpray
    (universalMetricSpraySet A D V delta) (isCompact_universalMetricSpraySet A D V delta) _ N
  intro q hq
  have hDet : q.1.det ≠ 0 := by
    intro he
    have hh := hq.2.2.2
    rw [he,abs_zero] at hh
    exact (not_le_of_gt hDelta) hh
  exact contDiffAt_universalMetricSpray q hDet

end ShrinkingSpheres
