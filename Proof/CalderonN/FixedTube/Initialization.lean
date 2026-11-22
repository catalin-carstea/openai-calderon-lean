module

public import Proof.CalderonN.FixedTube.Propagation

import Proof.CalderonN.QuantitativePhaseSweep
import Proof.CalderonN.FixedTube.JetContinuity
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

@[expose] def fixedSeparationSet (B d : ℝ) : Set ((X dim) × (X dim)) :=
  {p | ‖p.1‖ ≤ B ∧ ‖p.2‖ ≤ B ∧ d ≤ ‖p.1-p.2‖}

theorem isCompact_fixedSeparationSet (B d : ℝ) : IsCompact (fixedSeparationSet (dim := dim) B d) := by
  have h : fixedSeparationSet B d =
      (closedBall (0 : (X dim)) B ×ˢ closedBall (0 : (X dim)) B) ∩
        {q : (X dim) × (X dim) | d ≤ ‖q.1-q.2‖} := by
    ext q
    simp only [fixedSeparationSet,mem_ofPred_eq,mem_inter_iff,mem_prod,mem_closedBall_zero_iff,and_assoc]
  rw [h]
  exact ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right
    (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm)

@[expose] def coarseDomain (normal : I dim) (B d c : ℝ) : Set ((X dim) × (X dim)) :=
  {p | ‖p.1‖ < B ∧ ‖p.2‖ < B ∧ d < ‖p.1-p.2‖ ∧ min (p.1 normal) (p.2 normal) < c * ‖p.1-p.2‖}

theorem isOpen_coarseDomain (B d c : ℝ) : IsOpen (coarseDomain normal B d c) := by
  have cx : Continuous (fun p : (X dim) × (X dim) => p.1 normal) :=
    (EuclideanSpace.proj (𝕜 := ℝ) normal : (X dim) →L[ℝ] ℝ).continuous.comp continuous_fst
  have cy : Continuous (fun p : (X dim) × (X dim) => p.2 normal) :=
    (EuclideanSpace.proj (𝕜 := ℝ) normal : (X dim) →L[ℝ] ℝ).continuous.comp continuous_snd
  have cs : Continuous (fun p : (X dim) × (X dim) => ‖p.1-p.2‖) := (continuous_fst.sub continuous_snd).norm
  have ccs : Continuous (fun p : (X dim) × (X dim) => c * ‖p.1-p.2‖) := continuous_const.mul cs
  simpa only [coarseDomain,Set.ofPred_and] using
    (isOpen_lt (f := fun p : (X dim) × (X dim) => ‖p.1‖) continuous_fst.norm
      (g := fun _ : (X dim) × (X dim) => B) continuous_const).inter
    ((isOpen_lt continuous_snd.norm (g := fun _ : (X dim) × (X dim) => B) continuous_const).inter
      ((isOpen_lt (f := fun _ : (X dim) × (X dim) => d) continuous_const cs).inter
        (isOpen_lt (cx.min cy) ccs)))

private theorem continuous_tubeInverse (M e0 σ : ℝ) (hσ : 0 ≤ σ) :
    Continuous (tubeCoordinates normal M e0 σ hσ).symm := by
  have h : Continuous (fun q : (TubeBase dim) × ℝ =>
      (q.1.1 + tubeRadius normal M e0 q.2 σ q.1.1 • (q.1.2 : (X dim)),q.1.1)) :=
    ((continuous_fst.fst.add
      (((tubeRadius_continuous (normal := normal) M e0 σ hσ).comp (continuous_snd.prodMk continuous_fst.fst)).smul
        (continuous_subtype_val.comp continuous_fst.snd))).prodMk continuous_fst.fst)
  exact h.congr (fun q => (tubeCoordinates_symm_apply (normal := normal) M e0 σ hσ q).symm)

set_option maxHeartbeats 3900000 in
/-- Fixed-separation continuation given the coarse Green seed on bounded
positive separation ranges of the chart. A property of the chosen seed
is retained alongside agreement on the entire seed domain. -/
theorem exists_fixedSeparation_productSolution_of_coarse_with_bound
    {B d c η M : ℝ} (hB : 0 ≤ B) (hd : 0 < d) (hc : 0 < c)
    (hη : 0 < η) (hη10 : η ≤ 1/10) (hcη : 13*η ≤ c) (hM : B+3 < M)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁0 : g₁ 0 = 1) (hg₂0 : g₂ 0 = 1)
    (P : ℝ → ℝ → ℝ → ((X dim) × (X dim) → ℝ) → Prop) (wantBound : Bool)
    (hcoarse : ∀ B' > B, ∀ d' ∈ Ioo (0 : ℝ) d,
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∃ F,
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (coarseDomain normal B' d' c) F ∧
        P lam B' d' F ∧ (wantBound = true → ∀ q ∈ coarseDomain normal B' d' c, |F q| ≤ C₀)) :
    ∃ B' > B, ∃ d' ∈ Ioo (0 : ℝ) d, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∃ (O : Set ((X dim) × (X dim))) (F G : (X dim) × (X dim) → ℝ), IsOpen O ∧ fixedSeparationSet B d ⊆ O ∧
        coarseDomain normal B' d' c ⊆ O ∧
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (coarseDomain normal B' d' c) F ∧
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
        EqOn G F (coarseDomain normal B' d' c) ∧ P lam B' d' F ∧
        (wantBound = true → ∀ q ∈ fixedSeparationSet B d, |G q| ≤ C) := by
  obtain ⟨σ,T0,e0,hσ,hσ1,he0,he01,hcap,htop,hstrict⟩ :=
    exists_compact_dilated_tube_strict (normal := normal) hc hη hη10 hcη hd hB hM hg₁ hg₂ hg₁0 hg₂0
  let amin : ℝ := min 1 (d / (2*(M+B+B^2)^2))
  let amax : ℝ := 2/c+1
  let lo : ℝ := amin/2
  let hi : ℝ := amax+1
  let e := tubeCoordinates normal M e0 σ hσ.le
  let K := tubeBaseSet normal M e0 B T0
  let Q := e.symm '' (K ×ˢ Icc lo hi)
  have hUt : 0 < M+B+B^2 := by nlinarith [sq_nonneg B]
  have hamin : 0 < amin := lt_min one_pos (div_pos hd (mul_pos two_pos (sq_pos_of_pos hUt)))
  have hmax : 1 < amax := lt_add_of_pos_left _ (div_pos two_pos hc)
  have hab : amin ≤ amax := (min_le_left _ _).trans hmax.le
  have hlo : 0 < lo := half_pos hamin
  have hahi : amax < hi := lt_add_one _
  have hk : IsCompact K := isCompact_tubeBaseSet he0 hB
  have hQ : IsCompact Q := (hk.prod isCompact_Icc).image (continuous_tubeInverse (normal := normal) M e0 σ hσ.le)
  obtain ⟨Rq,hRq⟩ := (Metric.isBounded_iff_subset_closedBall (0 : (X dim) × (X dim))).mp hQ.isBounded
  let B' := max B Rq + 1
  let d' := min d lo / 2
  have hB' : B < B' := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hRq' : Rq < B' := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hd' : d' ∈ Ioo (0 : ℝ) d :=
    ⟨half_pos (lt_min hd hlo),(half_lt_self (lt_min hd hlo)).trans_le (min_le_left _ _)⟩
  have hdlo : d' < lo := (half_lt_self (lt_min hd hlo)).trans_le (min_le_right _ _)
  have hheight (z : (TubeBase dim)) (hz : z ∈ K) : 1 ≤ tubeHeight normal M e0 z.1 :=
    (tube_base_height he0.le hM hz.1 hz.2).1
  have hunfold (z : (TubeBase dim)) (a : ℝ) : e.symm (z,a) = tubePoint normal M e0 σ (a,z.1,(z.2 : (X dim))) :=
    tubeCoordinates_symm_apply (normal := normal) M e0 σ hσ.le (z,a)
  have hsep (z : (TubeBase dim)) (hz : z ∈ K) (a : ℝ) (ha : a ∈ Icc lo hi) :
      d' < ‖(e.symm (z,a)).1 - (e.symm (z,a)).2‖ := by
    have ha₀ := hlo.le.trans ha.1
    have hp := Real.one_le_rpow (hheight z hz) (by linarith : 0 ≤ 1+σ)
    rw [hunfold,tubePoint,add_sub_cancel_left,norm_smul,
      mem_sphere_zero_iff_norm.mp z.2.property,mul_one,Real.norm_eq_abs,tubeRadius,
      abs_of_nonneg (mul_nonneg ha₀ (zero_le_one.trans hp))]
    exact (hdlo.trans_le ha.1).trans_le (le_mul_of_one_le_right ha₀ hp)
  have hcoarse' (a : ℝ) (ha : a ∈ Ioo lo hi) (z : (TubeBase dim)) (hz : z ∈ K) :
      let p := tubePoint normal M e0 σ (a,z.1,(z.2 : (X dim)))
      p ∈ coarseDomain normal B' d' c ↔ min (p.1 normal) (p.2 normal) < c * ‖p.1-p.2‖ := by
    rw [← hunfold z a]
    have hpQ : e.symm (z,a) ∈ Q := ⟨(z,a),⟨hz,ha.1.le,ha.2.le⟩,rfl⟩
    have hpB := hRq hpQ
    rw [mem_closedBall,dist_zero_right,norm_prod_le_iff] at hpB
    exact ⟨fun h => h.2.2.2,fun h =>
      ⟨hpB.1.trans_lt hRq',hpB.2.trans_lt hRq',hsep z hz a ⟨ha.1.le,ha.2.le⟩,h⟩⟩
  have hcover : fixedSeparationSet B d ⊆
      coarseDomain normal B' d' c ∪ e.symm '' (K ×ˢ Ioc amin amax) := by
    intro p hp
    have hy₂ : |p.2 normal| ≤ B := (abs_coord_le_norm _ _).trans hp.2.1
    have hh : transversePair normal p.2 p.2 ≤ B^2 :=
      (transversePair_le_norm_sq normal p.2).trans
        (pow_le_pow_left₀ (norm_nonneg p.2) hp.2.1 2)
    have hty := tube_target_height_le (M := M) he0.le he01 (abs_le.mp hy₂).2 hh
    have hy : -B-1 ≤ p.2 normal := by linarith [(abs_le.mp hy₂).1]
    have hty' := (tube_base_height (T0 := tubeHeight normal M e0 p.2) he0.le hM hy le_rfl).1
    have hne : p.1 ≠ p.2 := sub_ne_zero.mp (norm_ne_zero_iff.mp (hd.trans_le hp.2.2).ne')
    have hsource : p ∈ e.source := by
      rw [show e.source = _ from tubeCoordinates_source (normal := normal) M e0 σ hσ.le]
      exact ⟨zero_lt_one.trans_le hty',hne⟩
    let z := (e p).1
    let a := (e p).2
    have hz : z ∈ K := by
      have hz' : z.1 = p.2 := tubeCoordinates_center (normal := normal) M e0 σ hσ.le p
      exact ⟨by rwa [hz'], by rw [hz']; exact hty.trans hcap.le⟩
    have ha : amin < a := by
      change amin < (e p).2
      rw [show (e p).2 = _ from tubeCoordinates_level (normal := normal) M e0 σ hσ.le p]
      exact tube_target_level_gt hd hp.2.2 hty' hty hσ.le hσ1
    have hp' : e.symm (z,a) = p := e.left_inv hsource
    by_cases hma : a ≤ amax
    · exact Or.inr ⟨(z,a),⟨hz,ha,hma⟩,hp'⟩
    · have hs : min (p.1 normal) (p.2 normal) < c * ‖p.1-p.2‖ := by
        rw [← hp',hunfold]
        exact tube_amax_level_in_seed hc (by linarith) he0.le (hheight z hz) hσ.le
          (le_of_not_ge hma) (mem_sphere_zero_iff_norm.mp z.2.property)
      exact Or.inl ⟨hp.1.trans_lt hB',hp.2.1.trans_lt hB',hd'.2.trans_le hp.2.2,hs⟩
  classical
  let S := coarseDomain normal B' d' c
  have hS : IsOpen S := isOpen_coarseDomain _ _ _
  obtain ⟨C₀,hC₀,hCoarse⟩ := hcoarse B' hB' d' hd'
  let gA := dilatedMetric g₁
  let gB := dilatedMetric g₂
  let Spec (lam : ℝ) (G : (X dim) × (X dim) → ℝ) : Prop :=
    ∃ (O : Set ((X dim) × (X dim))) (F : (X dim) × (X dim) → ℝ), IsOpen O ∧
      S ∪ e.symm '' (K ×ˢ Icc amin amax) ⊆ O ∧
      ProductSolutionOn (gA lam) (gB lam) S F ∧
      ProductSolutionOn (gA lam) (gB lam) O G ∧ EqOn G F S ∧ P lam B' d' F ∧
      (wantBound = true → ∀ q ∈ S, |F q| ≤ C₀)
  have hExists : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∃ G, Spec lam G := by
    filter_upwards [hstrict,hCoarse] with lam hs hc' hpos
    obtain ⟨F,hF,hFP,hFB⟩ := hc' hpos
    obtain ⟨O,hO,hOc,G,hG,hGF⟩ := exists_productSolution_fixedTube (normal := normal) he0 hB hM hσ.le hc hlo.le
      (half_lt_self hamin) hab hahi le_rfl htop
      (smoothMetric_dilatedMetric hg₁ lam) (smoothMetric_dilatedMetric hg₂ lam)
      hS F hF hcoarse' (fun a ha z hz h =>
        hs (a,z.1,(z.2 : (X dim))) (mem_sphere_zero_iff_norm.mp z.2.property) hz.1 hz.2 ha.1 ha.2 h)
    exact ⟨G,O,F,hO,hOc,hF,hG,hGF,hFP,hFB⟩
  let G (lam : ℝ) : (X dim) × (X dim) → ℝ :=
    if h : ∃ G, Spec lam G then Classical.choose h else 0
  have hSpec : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → Spec lam (G lam) := by
    filter_upwards [hExists] with lam hEx hpos
    have h := hEx hpos
    dsimp only [G]
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  have hBnd : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      wantBound = true → ∀ q ∈ fixedSeparationSet B d, |G lam q| ≤ C := by
    by_cases hb : wantBound = true
    · have hTarget : K ×ˢ Ico amin hi ⊆ e.target := by
        intro q hq
        rw [show e.target = _ from tubeCoordinates_target (normal := normal) M e0 σ hσ.le]
        exact ⟨zero_lt_one.trans_le (hheight q.1 hq.1),hamin.trans_le hq.2.1⟩
      have hTop : e.symm '' (K ×ˢ Ioo amax hi) ⊆ S := by
        rintro q ⟨⟨z,a⟩,⟨hz,ha⟩,rfl⟩
        rw [hunfold]
        exact (hcoarse' a ⟨((half_lt_self hamin).trans_le hab).trans ha.1,ha.2⟩ z hz).2
          (tube_amax_level_in_seed hc (by linarith) he0.le (hheight z hz) hσ.le ha.1.le
            (mem_sphere_zero_iff_norm.mp z.2.property))
      have hSide : e.symm '' ((K \ interior K) ×ˢ Ioc amin amax) ⊆ S := by
        rintro q ⟨⟨z,a⟩,⟨⟨hz,hzi⟩,ha⟩,rfl⟩
        have hw := mem_sphere_zero_iff_norm.mp z.2.property
        have ha' : a ∈ Ioo lo hi := ⟨(half_lt_self hamin).trans ha.1,ha.2.trans_lt hahi⟩
        rw [hunfold]
        apply (hcoarse' a ha' z hz).2
        by_cases hbottom : -B - 1 < z.1 normal
        · have heq : tubeHeight normal M e0 z.1 = T0 := le_antisymm hz.2
            (not_lt.mp fun ht => hzi (mem_interior_tubeBaseSet hbottom ht))
          exact tube_top_face_in_seed hc (by linarith) he0.le
            (zero_lt_one.trans_le (hheight z hz)) hamin.le ha.1.le (by rwa [heq]) hw
        · have hy : z.1 normal < 0 := by linarith [not_lt.mp hbottom]
          exact tube_bottom_face_in_seed hc
            (mul_pos (hamin.trans ha.1) (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hheight z hz)) _)) hy hw
      have hSol : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
          ProductSolutionOn (gA lam) (gB lam) (e.symm '' (interior K ×ˢ Ioo amin hi)) (G lam) := by
        filter_upwards [hSpec] with lam h hlam
        obtain ⟨O,F,hO,hOc,_,hG,_,_,_⟩ := h hlam
        apply hG.mono
        rintro q ⟨⟨z,a⟩,⟨hz,ha⟩,rfl⟩
        apply hOc
        by_cases ht : a ≤ amax
        · exact Or.inr ⟨(z,a),⟨interior_subset hz,ha.1.le,ht⟩,rfl⟩
        · exact Or.inl (hTop ⟨(z,a),⟨interior_subset hz,lt_of_not_ge ht,ha.2⟩,rfl⟩)
      have hSeed : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ q ∈ S, |G lam q| ≤ C₀ := by
        filter_upwards [hSpec] with lam h hlam q hq
        obtain ⟨_,_,_,_,_,_,hEq,_,hBnd⟩ := h hlam
        rw [hEq hq]
        exact hBnd hb q hq
      have hCovers : fixedSeparationSet B d ⊆ S ∪ e.symm '' (K ×ˢ Ioo amin hi) :=
        hcover.trans (union_subset_union Subset.rfl (image_mono
          (Set.prod_mono Subset.rfl (fun a ha => ⟨ha.1,ha.2.trans_lt hahi⟩))))
      have hSmooth : ∀ a ∈ Ioc amin amax, ContDiffOn ℝ ∞ (tubePhase normal M e0 a σ)
          (e.symm '' (interior K ×ˢ Ioo amin hi)) := by
        intro a _
        rintro _ ⟨⟨z,t⟩,⟨hz,_⟩,rfl⟩
        exact (contDiffAt_tubePhase (normal := normal) (a := a) (σ := σ)
          (z := e.symm (z,t)) (by rw [hunfold]; exact zero_lt_one.trans_le (hheight z (interior_subset hz)))).contDiffWithinAt
      have hZero : ∀ a ∈ Ioc amin amax, ∀ z ∈ interior K,
          tubePhase normal M e0 a σ (e.symm (z,a)) = 0 := by
        intro a ha z hz
        rw [show e = tubeCoordinates normal M e0 σ hσ.le from rfl,
          tubePhase_along_vertical (normal := normal) hσ.le z (zero_lt_one.trans_le (hheight z (interior_subset hz))) (hamin.trans ha.1).le]
        ring
      have hSign : ∀ a ∈ Ioc amin amax, ∀ z ∈ interior K, ∀ t ∈ Ioo amin hi,
          0 < tubePhase normal M e0 a σ (e.symm (z,t)) → a < t := by
        intro a ha z hz t ht
        have hP := zero_lt_one.trans_le (hheight z (interior_subset hz))
        rw [show e = tubeCoordinates normal M e0 σ hσ.le from rfl,
          tubePhase_along_vertical (normal := normal) hσ.le z hP (hamin.trans ht.1).le]
        have hp := pow_pos (Real.rpow_pos_of_pos hP (1+σ)) 2
        rw [div_pos_iff_of_pos_right (by norm_num),mul_pos_iff_of_pos_right hp,sub_pos,
          pow_lt_pow_iff_left₀ (hamin.trans ha.1).le (hamin.trans ht.1).le two_ne_zero]
        exact id
      have hStrict : ∀ a ∈ Ioc amin amax, ∀ z ∈ interior K, e.symm (z,a) ∉ S →
          ProductStrictHessianAt (gA 0) (gB 0) (tubePhase normal M e0 a σ) (e.symm (z,a)) := by
        intro a ha z hz hn
        have ha' : a ∈ Ioo lo hi := ⟨(half_lt_self hamin).trans ha.1,ha.2.trans_lt hahi⟩
        rw [hunfold] at hn ⊢
        exact hstrict.self_of_nhds (a,z.1,(z.2 : (X dim))) (mem_sphere_zero_iff_norm.mp z.2.property)
          (interior_subset hz).1 (interior_subset hz).2 ha.1.le ha.2
          (le_of_not_gt fun h => hn ((hcoarse' a ha' z (interior_subset hz)).2 h))
      obtain ⟨C,hC,h⟩ := exists_uniform_bound_across_phase_cylinder e hk hS hab hahi hTarget
        hTop hSide (smoothMetric_dilatedMetric hg₁) (smoothMetric_dilatedMetric hg₂)
        (contDiff_dilatedMetric_entry hg₁) (contDiff_dilatedMetric_entry hg₂)
        (contDiff_dilatedMetric_divergenceCoeff hg₁) (contDiff_dilatedMetric_divergenceCoeff hg₂)
        G hSol hC₀ hSeed (fun a => tubePhase normal M e0 a σ) hSmooth hZero hSign hStrict
        (isCompact_fixedSeparationSet B d) hCovers
      exact ⟨C,hC,h.mono fun _ h hl _ => h hl⟩
    · exact ⟨0,le_rfl,Eventually.of_forall (fun _ _ h => (hb h).elim)⟩
  obtain ⟨C,hC,hBnd⟩ := hBnd
  refine ⟨B',hB',d',hd',C,hC,?_⟩
  filter_upwards [hSpec,hBnd] with lam hSpec hBnd hPos
  obtain ⟨O,F,hO,hOc,hF,hG,hEq,hP,_⟩ := hSpec hPos
  refine ⟨O,F,G lam,hO,?_,subset_union_left.trans hOc,hF,hG,hEq,hP,hBnd hPos⟩
  have hI : Ioc amin amax ⊆ Icc amin amax := fun a ha => ⟨ha.1.le,ha.2⟩
  exact hcover.trans ((union_subset_union Subset.rfl (image_mono
    (Set.prod_mono Subset.rfl hI))).trans hOc)

/-- Fixed-separation continuation given the coarse Green seed on bounded
positive separation ranges of the chart. A property of the chosen seed
is retained alongside agreement on the entire seed domain. -/
theorem exists_fixedSeparation_productSolution_of_coarse
    {B d c η M : ℝ} (hB : 0 ≤ B) (hd : 0 < d) (hc : 0 < c)
    (hη : 0 < η) (hη10 : η ≤ 1/10) (hcη : 13*η ≤ c) (hM : B+3 < M)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁0 : g₁ 0 = 1) (hg₂0 : g₂ 0 = 1)
    (P : ℝ → ℝ → ℝ → ((X dim) × (X dim) → ℝ) → Prop)
    (hcoarse : ∀ B' > B, ∀ d' ∈ Ioo (0 : ℝ) d,
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∃ F,
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (coarseDomain normal B' d' c) F ∧ P lam B' d' F) :
    ∃ B' > B, ∃ d' ∈ Ioo (0 : ℝ) d, ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∃ (O : Set ((X dim) × (X dim))) (F G : (X dim) × (X dim) → ℝ), IsOpen O ∧ fixedSeparationSet B d ⊆ O ∧
        coarseDomain normal B' d' c ⊆ O ∧
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (coarseDomain normal B' d' c) F ∧
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
        EqOn G F (coarseDomain normal B' d' c) ∧ P lam B' d' F := by
  have hCore := exists_fixedSeparation_productSolution_of_coarse_with_bound hB hd hc hη hη10 hcη hM
    hg₁ hg₂ hg₁0 hg₂0 P false (fun B' hB' d' hd' =>
      ⟨0,le_rfl,(hcoarse B' hB' d' hd').mono fun _ h hp => by
        obtain ⟨F,hF,hP⟩ := h hp
        exact ⟨F,hF,hP,fun h => by cases h⟩⟩)
  obtain ⟨B',hB',d',hd',_,_,h⟩ := hCore
  refine ⟨B',hB',d',hd',h.mono fun _ h hp => ?_⟩
  obtain ⟨O,F,G,hO,hS,hC,hF,hG,hEq,hP,_⟩ := h hp
  exact ⟨O,F,G,hO,hS,hC,hF,hG,hEq,hP⟩

end CalderonN.FixedTube
