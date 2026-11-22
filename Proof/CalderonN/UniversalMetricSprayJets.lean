module

public import Proof.CalderonN.UniformCanonicalFrameJets
public import Proof.CalderonN.NormalGeodesicPhase

import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ConnectionOperatorBounds
import Proof.CalderonN.CenterJetCalculus
import Mathlib.Tactic

/-! The rational geodesic spray on its finite-dimensional input space,
adapted from the checked Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev MetricConnectionInput (dim : ℕ) := (Mat dim) × ((X dim) →L[ℝ] (Mat dim))
abbrev MetricSprayInput (dim : ℕ) := (Mat dim) × (((X dim) →L[ℝ] (Mat dim)) × (X dim))

def universalChristoffel (q : MetricConnectionInput dim) (k i j : (I dim)) : ℝ :=
  (∑ l, q.1⁻¹ k l*((q.2 (axis i)) l j+(q.2 (axis j)) i l-(q.2 (axis l)) i j))/2

def universalMetricConnection (q : MetricConnectionInput dim) : (X dim) →L[ℝ] (X dim) →L[ℝ] (X dim) :=
  ∑ i,∑ j,∑ k,universalChristoffel q k i j • coordinateBilinearAtom i j k

def universalMetricSpray (q : MetricSprayInput dim) : (X dim) × (X dim) :=
  (q.2.2,-universalMetricConnection (q.1,q.2.1) q.2.2 q.2.2)

lemma contDiffAt_universalChristoffel (q : MetricConnectionInput dim)
    (hDet : q.1.det ≠ 0) (k i j : (I dim)) :
    ContDiffAt ℝ ∞ (fun r => universalChristoffel r k i j) q := by
  let U : Set (MetricConnectionInput dim) := {r | r.1.det ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage (contDiffOn_univ.mp (contDiffOn_det_of_entries (fun i j =>
    (contDiff_pi.mp (contDiff_pi.mp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : MetricConnectionInput dim → Mat dim)) i) j).contDiffOn))).continuous
  have hA (a b : (I dim)) : ContDiffOn ℝ ∞ (fun r : MetricConnectionInput dim => r.1 a b) U :=
    (contDiff_pi.mp (contDiff_pi.mp contDiff_fst a) b).contDiffOn
  have hInv (a b : (I dim)) : ContDiffAt ℝ ∞ (fun r : MetricConnectionInput dim => r.1⁻¹ a b) q :=
    (contDiffOn_inv_entry_of_entries hA (fun r hr => hr) a b).contDiffAt
      (hU.mem_nhds hDet)
  have hD (a b c : (I dim)) : ContDiffAt ℝ ∞ (fun r : MetricConnectionInput dim => (r.2 (axis a)) b c) q :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_snd.clm_apply contDiffAt_const) b) c
  exact (ContDiffAt.sum (fun l _ => (hInv k l).mul (((hD i l j).add (hD j i l)).sub (hD l i j)))).div_const 2

lemma contDiffAt_universalMetricConnection (q : MetricConnectionInput dim) (hDet : q.1.det ≠ 0) :
    ContDiffAt ℝ ∞ universalMetricConnection q := by
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => ContDiffAt.sum
    (fun k _ => (contDiffAt_universalChristoffel q hDet k i j).smul contDiffAt_const)))

lemma contDiffAt_universalMetricSpray (q : MetricSprayInput dim) (hDet : q.1.det ≠ 0) :
    ContDiffAt ℝ ∞ universalMetricSpray q := by
  have hC := (contDiffAt_universalMetricConnection (q.1,q.2.1) hDet).comp q
    (contDiffAt_fst.prodMk contDiffAt_snd.fst)
  exact contDiffAt_snd.snd.prodMk ((hC.clm_apply contDiffAt_snd.snd).clm_apply contDiffAt_snd.snd).neg

lemma universalMetricConnection_actual (g : (MetricField dim)) (x : (X dim)) (hg : ContDiffAt ℝ ∞ g x) :
    universalMetricConnection (g x,fderiv ℝ g x) = connectionBilinear g x := by
  have hD (k i j : I dim) : fderiv ℝ (fun y => g y i j) x (axis k) =
      (fderiv ℝ g x (axis k)) i j := by
    have h := (matrixEntryL i j).hasFDerivAt.comp x (hg.differentiableAt (by simp)).hasFDerivAt
    have hEq : (matrixEntryL i j) ∘ g = fun y => g y i j :=
      funext fun y => matrixEntryL_apply i j (g y)
    rw [hEq] at h
    rw [h.fderiv,ContinuousLinearMap.comp_apply,matrixEntryL_apply]
  have hΓ (k i j : I dim) : universalChristoffel (g x,fderiv ℝ g x) k i j = christoffel g x k i j := by
    simp only [universalChristoffel,christoffel,coordDeriv,hD]
  simp only [universalMetricConnection,hΓ,connectionBilinear,coordinateBilinearAtom]

lemma universalMetricSpray_actual (g : (MetricField dim)) (x v : (X dim)) (hg : ContDiffAt ℝ ∞ g x) :
    universalMetricSpray (g x,(fderiv ℝ g x,v)) = coordinateGeodesicSpray g (x,v) := by
  rw [universalMetricSpray,universalMetricConnection_actual g x hg,connectionBilinear_apply]
  rfl

/-- The finite-dimensional input locus carries the ellipticity and finite
jet budgets. The determinant stays positive throughout it. -/
@[expose] def universalMetricSpraySet (dim : ℕ) (K R : ℝ) : Set (MetricSprayInput dim) :=
  ellipticMatrixLocus dim K R ×ˢ
    (closedBall (0 : X dim →L[ℝ] Mat dim) R ×ˢ closedBall (0 : X dim) K)

theorem exists_universalMetricSpray_jet_bound (K R : ℝ) (hK : 0 < K) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, n ≤ N → ∀ q ∈ universalMetricSpraySet dim K R,
      ‖iteratedFDeriv ℝ n universalMetricSpray q‖ ≤ C := by
  let J := universalMetricSpraySet dim K R
  have hJ : IsCompact J := (isCompact_ellipticMatrixLocus dim K R).prod
    ((isCompact_closedBall (0 : X dim →L[ℝ] Mat dim) R).prod (isCompact_closedBall (0 : X dim) K))
  have hSmooth (q : MetricSprayInput dim) (hq : q ∈ J) : ContDiffAt ℝ ∞ universalMetricSpray q :=
    contDiffAt_universalMetricSpray q (ellipticMatrixLocus_posDef hK hq.1).det_pos.ne'
  choose A hA using fun n : Fin (N+1) => hJ.exists_bound_of_continuousOn
    (fun q hq => ((hSmooth q hq).continuousAt_iteratedFDeriv (k:=n.val) (by simp)).continuousWithinAt)
  let C := 1 + ∑ n, |A n|
  refine ⟨C,le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _),?_⟩
  intro n hn q hq
  let i : Fin (N+1) := ⟨n,by omega⟩
  exact (hA i q hq).trans ((le_abs_self _).trans
    ((Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1))))

end CalderonN
