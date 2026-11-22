module

public import Proof.Manuscript.ScalarFamilyCutoff
public import Proof.Manuscript.ScalarUniformCross

import Proof.CalderonN.BallRegularity.SpatialJetFields
import Proof.CalderonN.CompactEllipticity
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric CalderonN
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

theorem SmoothFamilyOn.contDiff_principal_univ {L : ℝ → ScalarElliptic n}
    (hL : SmoothFamilyOn L univ) (i j : I n) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => (L q.1).principalMatrix q.2 i j) := by
  have hG (i j : I n) :
      ContDiffOn ℝ ∞ (fun q : ℝ × X n => (L q.1).metric q.2 i j) univ :=
    (hL.2.1 i j).mono (by simp)
  exact contDiffOn_univ.mp (contDiffOn_inv_entry_of_entries hG
    (fun q _ => ((hL.1 q.1).1.2 q.2 (mem_univ _)).det_pos.ne') i j)

theorem SmoothFamilyOn.contDiff_first_univ {L : ℝ → ScalarElliptic n}
    (hL : SmoothFamilyOn L univ) (i : I n) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => (L q.1).first q.2 i) :=
  contDiffOn_univ.mp ((hL.2.2.1 i).mono (by simp))

theorem SmoothFamilyOn.contDiff_zeroth_univ {L : ℝ → ScalarElliptic n}
    (hL : SmoothFamilyOn L univ) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => (L q.1).zeroth q.2) :=
  contDiffOn_univ.mp (hL.2.2.2.mono (by simp))

theorem SmoothFamilyOn.contDiff_divergence_univ {L : ℝ → ScalarElliptic n}
    (hL : SmoothFamilyOn L univ) (i j : I n) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => divergenceCoeff (L q.1).metric q.2 i j) := by
  have hG (i j : I n) :
      ContDiffOn ℝ ∞ (fun q : ℝ × X n => (L q.1).metric q.2 i j) univ :=
    (hL.2.1 i j).mono (by simp)
  have hV : ContDiff ℝ ∞ (fun q : ℝ × X n => chartVolume (L q.1).metric q.2) :=
    contDiffOn_univ.mp ((contDiffOn_det_of_entries hG).sqrt
      (fun q _ => ((hL.1 q.1).1.2 q.2 (mem_univ _)).det_pos.ne'))
  exact hV.mul (hL.contDiff_principal_univ i j)

theorem SmoothFamilyOn.contDiff_chartVolume_univ {L : ℝ → ScalarElliptic n}
    (hL : SmoothFamilyOn L univ) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => chartVolume (L q.1).metric q.2) := by
  have hG (i j : I n) :
      ContDiffOn ℝ ∞ (fun q : ℝ × X n => (L q.1).metric q.2 i j) univ :=
    (hL.2.1 i j).mono (by simp)
  exact contDiffOn_univ.mp ((contDiffOn_det_of_entries hG).sqrt
    (fun q _ => ((hL.1 q.1).1.2 q.2 (mem_univ _)).det_pos.ne'))

/-- Finite spatial derivative bounds chosen from the reference slice alone. -/
theorem exists_reference_spatial_jet_bounds {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : Type*} [Fintype J] {K : Set E} (hK : IsCompact K) {F₀ : J → E → ℝ}
    (hF₀ : ∀ j, ContDiff ℝ ∞ (F₀ j)) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : J → ℝ × E → ℝ, (∀ j, ContDiff ℝ ∞ (F j)) →
      (∀ j, (fun x => F j (0,x)) = F₀ j) →
      ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ K, ∀ j k, k ≤ N →
        ‖iteratedFDeriv ℝ k (fun y => F j (s,y)) x‖ ≤ C := by
  classical
  let h (j : J × Fin (N+1)) (x : E) := ‖iteratedFDeriv ℝ j.2.val (F₀ j.1) x‖
  have hBound (j : J × Fin (N+1)) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ K, h j x ≤ A := by
    obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn
      ((((hF₀ j.1).continuous_iteratedFDeriv (m := j.2.val) (by simp)).norm).continuousOn)
    exact ⟨max A 0,le_max_right _ _,fun x hx =>
      (le_abs_self _).trans ((hA x hx).trans (le_max_left _ _))⟩
  choose A hA hRef using hBound
  let C := 1 + ∑ j, A j
  have hC : 0 < C := zero_lt_one.trans_le
    (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hA j))
  refine ⟨C,hC,fun F hF he => ?_⟩
  have hEvt : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ K, ∀ j : J × Fin (N+1),
      ‖SpatialJetFields.spatialJetField j.2.val (F j.1) (s,x)‖ ≤ C := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    apply Filter.eventually_all.mpr
    intro j
    have hCont : Continuous (fun q => ‖SpatialJetFields.spatialJetField j.2.val (F j.1) q‖) :=
      (SpatialJetFields.contDiff_spatialJetField _ _ (hF j.1)).continuous.norm
    have hCenter : ‖SpatialJetFields.spatialJetField j.2.val (F j.1) (0,x)‖ < C := by
      rw [SpatialJetFields.spatialJetField_eq_iteratedFDeriv _ _ (hF j.1),he j.1]
      exact ((hRef j x hx).trans (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ j))).trans_lt
        (lt_one_add _)
    have hev : ∀ᶠ q : ℝ × E in 𝓝 ((0 : ℝ),x),
        ‖SpatialJetFields.spatialJetField j.2.val (F j.1) q‖ < C :=
      hCont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hCenter)
    exact hev.mono fun _ hq => hq.le
  filter_upwards [hEvt] with s hs x hx j k hk
  rw [← SpatialJetFields.spatialJetField_eq_iteratedFDeriv k (F j) (hF j) s x]
  exact hs x hx (j,⟨k,Nat.lt_succ_of_le hk⟩)

set_option maxHeartbeats 1500000 in
/-- The ellipticity floor on a fixed compact set is chosen from the
reference principal symbol, and holds eventually for every smooth path. -/
theorem exists_reference_principal_floor {K : Set (X n)} (hK : IsCompact K)
    {L₀ : ScalarElliptic n} (h₀ : L₀.SmoothOn univ) :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℝ → ScalarElliptic n, SmoothFamilyOn L univ → L 0 = L₀ →
      ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ K, ∀ v : X n, a * ‖v‖^2 ≤ metricPair (L s).principalMatrix x v v := by
  obtain ⟨a,ha,hRef⟩ := Elliptic.lower_ellipticity_on_compact
    (a := fun i j x => L₀.principalMatrix x i j)
    (fun i j => (contDiffOn_univ.mp (contDiffOn_metric_inv_entry h₀.1 i j)).continuous)
    hK (fun x _ => (h₀.1.2 x (mem_univ _)).inv)
  let S := sphere (0 : X n) 1
  refine ⟨a/2,half_pos ha,fun L hL he => ?_⟩
  let Q (q : ℝ × (X n × X n)) := metricPair (L q.1).principalMatrix q.2.1 q.2.2 q.2.2
  have hQ : Continuous Q := by
    unfold Q metricPair
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((hL.contDiff_principal_univ i j).continuous.comp (continuous_fst.prodMk continuous_snd.fst)).mul
        ((EuclideanSpace.proj i).continuous.comp continuous_snd.snd)).mul
        ((EuclideanSpace.proj j).continuous.comp continuous_snd.snd)
  have hEvt : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q ∈ K ×ˢ S, a/2 ≤ Q (s,q) := by
    apply (hK.prod (isCompact_sphere _ _)).eventually_forall_of_forall_eventually
    intro q hq
    have hn : ‖q.2‖ = 1 := mem_sphere_zero_iff_norm.mp hq.2
    have h := hRef q.1 hq.1 (fun i => q.2 i)
    rw [← EuclideanSpace.real_norm_sq_eq,hn,one_pow,mul_one] at h
    have hx : a ≤ Q (0,q) := by
      simp only [Q,he,metricPair]
      exact h.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    have hev : ∀ᶠ r : ℝ × (X n × X n) in 𝓝 ((0 : ℝ),q), a/2 < Q r :=
      hQ.continuousAt.preimage_mem_nhds (Ioi_mem_nhds ((half_lt_self ha).trans_le hx))
    exact hev.mono fun _ hr => hr.le
  filter_upwards [hEvt] with s hs x hx v
  by_cases hv : v = 0
  · simp [hv,metricPair]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : u ∈ S := by
    rw [mem_sphere_zero_iff_norm]
    change ‖‖v‖⁻¹ • v‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hvn.le),inv_mul_cancel₀ hvn.ne']
  have heq : v = ‖v‖ • u := by unfold u; rw [smul_smul,mul_inv_cancel₀ hvn.ne',one_smul]
  have hHom : metricPair (L s).principalMatrix x v v = ‖v‖^2 * Q (s,x,u) := by
    conv_lhs => rw [heq]
    simp only [Q,metricPair,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hHom,mul_comm (a/2)]
  exact mul_le_mul_of_nonneg_left (hs (x,u) ⟨hx,hu⟩) (sq_nonneg _)

set_option maxHeartbeats 2000000 in
/-- Finite scalar coefficient budgets prepared on a compact room before
choosing a smooth perturbation of its reference operator. -/
theorem exists_reference_scalar_coefficient_budget {K : Set (X n)} (hK : IsCompact K)
    {L₀ : ScalarElliptic n} (h₀ : L₀.SmoothOn univ) (N : ℕ) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
      ∀ L : ℝ → ScalarElliptic n, SmoothFamilyOn L univ → L 0 = L₀ →
      ∀ᶠ s in 𝓝 (0 : ℝ), (L s).CoefficientBound K a A N := by
  obtain ⟨a,ha,hFloor⟩ := exists_reference_principal_floor hK h₀
  let J := (I n × I n) ⊕ (I n ⊕ Unit)
  let F (L : ScalarElliptic n) (j : J) (x : X n) : ℝ :=
    Sum.elim (fun ij => L.principalMatrix x ij.1 ij.2)
      (Sum.elim (fun i => L.first x i) (fun _ => L.zeroth x)) j
  have hF (L : ℝ → ScalarElliptic n) (hL : SmoothFamilyOn L univ) (j : J) :
      ContDiff ℝ ∞ (fun q : ℝ × X n => F (L q.1) j q.2) := by
    rcases j with ij | (i | j)
    · exact hL.contDiff_principal_univ ij.1 ij.2
    · exact hL.contDiff_first_univ i
    · exact hL.contDiff_zeroth_univ
  have hRef (j : J) : ContDiff ℝ ∞ (F L₀ j) := by
    have hs := hF (fun _ => L₀) (smoothFamilyOn_const h₀) j
    exact hs.comp ((contDiff_const (c := (0 : ℝ))).prodMk
      (contDiff_id : ContDiff ℝ ∞ (id : X n → X n)))
  obtain ⟨A,hA,hDeriv⟩ := exists_reference_spatial_jet_bounds hK hRef N
  refine ⟨a,A,ha,hA,fun L hL he => ?_⟩
  have hF₀ (j : J) : (fun x => F (L 0) j x) = F L₀ j := by rw [he]
  filter_upwards [hFloor L hL he,hDeriv (fun j q => F (L q.1) j q.2) (hF L hL) hF₀] with s hs hDer
  refine ⟨hs,fun x hx j hj => ⟨fun i k => ?_,fun i => ?_,?_⟩⟩
  · exact hDer x hx (Sum.inl (i,k)) j hj
  · exact hDer x hx (Sum.inr (Sum.inl i)) j hj
  · exact hDer x hx (Sum.inr (Sum.inr ())) j hj

end CalderonPaper.ScalarElliptic
