module

public import Proof.CalderonN.UniversalMetricSprayJets
public import Proof.CalderonN.NormalCenterBoundaryChainRule

import Proof.CalderonN.CompactFiniteJets
import Mathlib.Tactic

/-! The normalized parallel-center map is a smooth finite-dimensional
function of the endpoint derivative and first metric jet. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev NormalEndpointDerivative (dim : ℕ) := (X dim × X dim) →L[ℝ] X dim
abbrev UniversalParallelCenterInput (dim : ℕ) := NormalEndpointDerivative dim × MetricSprayInput dim

@[expose] def parallelCenterVerticalInputL :
    NormalEndpointDerivative dim →L[ℝ] (X dim →L[ℝ] X dim) :=
  (ContinuousLinearMap.compL ℝ (X dim) (X dim × X dim) (X dim)).flip
    (ContinuousLinearMap.inr ℝ (X dim) (X dim))

@[expose] def universalParallelCenter (p : UniversalParallelCenterInput dim) : X dim →L[ℝ] X dim :=
  (parallelCenterVerticalInputL p.1).inverse.comp
    (p.1.comp ((ContinuousLinearMap.id ℝ (X dim)).prod
      (-((universalMetricConnection (p.2.1,p.2.2.1)).flip p.2.2.2))))

theorem universalParallelCenter_actual (g : MetricField dim) (E : X dim × X dim → X dim)
    (p : X dim × X dim) (hg : ContDiffAt ℝ ∞ g p.1) :
    universalParallelCenter (fderiv ℝ E p,(g p.1,(fderiv ℝ g p.1,p.2))) =
      normalizedParallelCenterJacobian g E p.1 p.2 := by
  rcases p with ⟨y,v⟩
  simp only [universalParallelCenter,universalMetricConnection_actual g y hg]
  rfl

theorem contDiffAt_universalParallelCenter (p : UniversalParallelCenterInput dim)
    (hDet : p.2.1.det ≠ 0) (hInv : (parallelCenterVerticalInputL p.1).IsInvertible) :
    ContDiffAt ℝ ∞ universalParallelCenter p := by
  let Γ (q : UniversalParallelCenterInput dim) := universalMetricConnection (q.2.1,q.2.2.1)
  have hΓ : ContDiffAt ℝ ∞ Γ p := (contDiffAt_universalMetricConnection _ hDet).comp p
    (contDiffAt_snd.fst.prodMk contDiffAt_snd.snd.fst)
  let flip := (ContinuousLinearMap.flipₗᵢ ℝ (X dim) (X dim) (X dim)).toContinuousLinearEquiv
  have hFlip : ContDiffAt ℝ ∞ (fun q => (Γ q).flip) p := flip.contDiff.contDiffAt.comp p hΓ
  have hΓv := (hFlip.clm_apply contDiffAt_snd.snd.snd).neg
  let prod := ContinuousLinearMap.prodL (𝕜:=ℝ) (E:=X dim) (F:=X dim) (G:=X dim) ℝ
  have hP : ContDiffAt ℝ ∞ (fun q => (ContinuousLinearMap.id ℝ (X dim)).prod (-(Γ q).flip q.2.2.2)) p :=
    prod.contDiff.contDiffAt.comp p (contDiffAt_const.prodMk hΓv)
  have hJ : ContDiffAt ℝ ∞ (fun q : UniversalParallelCenterInput dim => parallelCenterVerticalInputL q.1) p :=
    parallelCenterVerticalInputL.contDiff.contDiffAt.comp p contDiffAt_fst
  exact ((hInv.contDiffAt_map_inverse (n:=∞)).comp p hJ).clm_comp (contDiffAt_fst.clm_comp hP)

theorem invertible_of_near_chartIdentity (L : X dim →L[ℝ] X dim)
    (hSmall : ‖L-ContinuousLinearMap.id ℝ (X dim)‖ < 1) : L.IsInvertible := by
  have hInj : Function.Injective L := by
    intro u v huv
    have h0 : L (u-v) = 0 := by rw [map_sub,huv,sub_self]
    have h := (L-ContinuousLinearMap.id ℝ (X dim)).le_opNorm (u-v)
    rw [sub_apply,ContinuousLinearMap.id_apply,h0,zero_sub,norm_neg] at h
    by_contra hne
    have hP : 0 < ‖u-v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    exact (not_lt_of_ge h) ((mul_lt_mul_of_pos_right hSmall hP).trans_eq (one_mul _))
  have hSurj : Function.Surjective L := (LinearMap.injective_iff_surjective (f:=L.toLinearMap)).mp hInj
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hInj,hSurj⟩).toContinuousLinearEquiv,by ext; rfl⟩

theorem exists_uniform_universalParallelCenter_jets (K B D : ℝ) (hK : 0 < K) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : UniversalParallelCenterInput dim,
      ‖p.1‖ ≤ D → ‖parallelCenterVerticalInputL p.1-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ) →
      p.2 ∈ universalMetricSpraySet dim K B →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n universalParallelCenter p‖ ≤ C := by
  let J₀ : Set (NormalEndpointDerivative dim) := closedBall 0 D ∩
    {L | ‖parallelCenterVerticalInputL L-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ)}
  have hClosed : IsClosed {L : NormalEndpointDerivative dim |
      ‖parallelCenterVerticalInputL L-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ)} :=
    isClosed_le ((parallelCenterVerticalInputL.continuous.sub continuous_const).norm) continuous_const
  have hJ₀ : IsCompact J₀ := (isCompact_closedBall 0 D).inter_right hClosed
  have hJ₁ : IsCompact (universalMetricSpraySet dim K B) :=
    (isCompact_ellipticMatrixLocus dim K B).prod
      ((isCompact_closedBall (0:X dim →L[ℝ] Mat dim) B).prod (isCompact_closedBall (0:X dim) K))
  let J := J₀ ×ˢ universalMetricSpraySet dim K B
  have hJ : IsCompact J := hJ₀.prod hJ₁
  have hS (p : UniversalParallelCenterInput dim) (hp : p ∈ J) :
      ContDiffAt ℝ ∞ universalParallelCenter p :=
    contDiffAt_universalParallelCenter p (ellipticMatrixLocus_posDef hK hp.2.1).det_pos.ne'
      (invertible_of_near_chartIdentity _ (hp.1.2.trans_lt (by norm_num)))
  choose cs hcs using fun n : Fin (N+1) => hJ.exists_bound_of_continuousOn
    (fun p hp => ((hS p hp).continuousAt_iteratedFDeriv (k:=n.val) (by simp)).continuousWithinAt)
  let C := 1+∑ i, |cs i|
  refine ⟨C,le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _),?_⟩
  intro p hD hSmall hMetric n hn
  have hMem : p ∈ J := ⟨⟨by simpa only [mem_closedBall,dist_zero_right] using hD,hSmall⟩,hMetric⟩
  let i : Fin (N+1) := ⟨n,by omega⟩
  exact (hcs i p hMem).trans ((le_abs_self _).trans
    ((Finset.single_le_sum (f := fun k => |cs k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)))

end CalderonN
