module

public import Proof.CalderonN.FixedTube.CoarsePatch
public import Proof.CalderonN.FixedTube.CoarseCoverage

import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.ProductGluing
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

private theorem swap_preimage_lowerCross (B η : ℝ) :
    Prod.swap ⁻¹' lowerCross normal B η = lowerCross normal B η := by
  ext q
  constructor
  · rintro ⟨⟨hy,hx,hne⟩,h⟩
    exact ⟨⟨hx,hy,Ne.symm hne⟩,h.symm⟩
  · rintro ⟨⟨hx,hy,hne⟩,h⟩
    exact ⟨⟨hy,hx,Ne.symm hne⟩,h.symm⟩

private theorem lowerSidePairs_swap {η : ℝ} {q : (X dim) × (X dim)} (hq : q ∈ lowerSidePairs normal η) :
    q.swap ∈ lowerSidePairs normal η := by
  change min (q.1 normal) (q.2 normal) < -η at hq
  change min (q.2 normal) (q.1 normal) < -η
  rwa [min_comm]

set_option maxHeartbeats 2700000 in
/-- The two orientations glue to the actual bounded lower cross.
A fixed positive coarse slope works on every bounded positive
separation range. The comparison uses the larger patches along the
common downward interval. -/
theorem exists_glued_coarse_seed_with_bound
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1) :
    ∃ c₀ > 0, ∀ B d ηcap : ℝ, 0 < B → 0 < d → 0 < ηcap →
      ∃ M η : ℝ, B < M ∧ 0 < η ∧ η ≤ ηcap ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ F : (X dim) × (X dim) → ℝ,
          ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (lowerCross normal M η) F →
          ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ), IsOpen O ∧ coarseDomain normal B d c₀ ⊆ O ∧
            lowerCross normal M η ⊆ O ∧
            ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
            EqOn G F (lowerCross normal M η) ∧
            ∀ L : ℝ, 0 ≤ L → (∀ q ∈ lowerCross normal M η, (3/16 : ℝ)*d ≤ ‖q.1-q.2‖ → |F q| ≤ L) →
              ∀ q ∈ coarseDomain normal B d c₀, |G q| ≤ C*L := by
  classical
  obtain ⟨δ₁,hδ₁,hδ₁cap,hPatch₁⟩ := (exists_uniform_coarsePatch_with_bound (normal := normal)) hg₁ hg₂ h₁ h₂
  obtain ⟨δ₂,hδ₂,hδ₂cap,hPatch₂⟩ := (exists_uniform_coarsePatch_with_bound (normal := normal)) hg₂ hg₁ h₂ h₁
  let κ := min (1/100 : ℝ) (min δ₁ δ₂ / 10)
  have hκ : 0 < κ := lt_min (by norm_num) (div_pos (lt_min hδ₁ hδ₂) (by norm_num))
  have hκcap : κ ≤ 1/100 := min_le_left _ _
  have hκ₁ : κ ≤ δ₁/10 := (min_le_right _ _).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hκ₂ : κ ≤ δ₂/10 := (min_le_right _ _).trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  refine ⟨κ/4,by positivity,?_⟩
  intro B d ηcap hB hd hηcap
  let Ba := 2*B+1
  let s₀ := d/2
  let s₁ := 3*B+1
  let M := Ba+2*s₁+1
  let η := min ηcap (κ*d/8)
  have hM : B < M := by dsimp [M,Ba,s₁]; linarith
  have hη : 0 < η := lt_min hηcap (by positivity)
  have hηd : η ≤ κ*d/8 := min_le_right _ _
  refine ⟨M,η,hM,hη,min_le_left _ _,?_⟩
  by_cases hdb : d < 2*B
  · have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
    have hss : s₀ ≤ s₁ := by dsimp [s₀,s₁]; linarith
    obtain ⟨C₁,hC₁,hP₁⟩ := hPatch₁ Ba s₀ s₁ hs₀ hss
    obtain ⟨C₂,hC₂,hP₂⟩ := hPatch₂ Ba s₀ s₁ hs₀ hss
    let C := max 1 (max C₁ C₂)
    have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
    refine ⟨C,hC,?_⟩
    filter_upwards [hP₁,hP₂] with lam hp₁ hp₂ F hF
    let G₁ := dilatedMetric g₁ lam
    let G₂ := dilatedMetric g₂ lam
    have hG₁ := smoothMetric_dilatedMetric hg₁ lam
    have hG₂ := smoothMetric_dilatedMetric hg₂ lam
    have hFswap := hF.swap
    rw [(swap_preimage_lowerCross (normal := normal))] at hFswap
    have hηκ : η ≤ κ*s₀ := by dsimp [s₀]; nlinarith only [hηd,mul_pos hκ hd]
    have hηδ₁ : η < δ₁*s₀ :=
      hηκ.trans_lt (mul_lt_mul_of_pos_right (by linarith) hs₀)
    have hηδ₂ : η < δ₂*s₀ :=
      hηκ.trans_lt (mul_lt_mul_of_pos_right (by linarith) hs₀)
    let δ (b : Bool) := if b then δ₂ else δ₁
    have hκδ (b : Bool) : 5*κ < δ b := by
      cases b
      · change 5*κ < δ₁
        linarith
      · change 5*κ < δ₂
        linarith
    let Iₐ := Bool × CoarseAnchor normal Ba s₀ s₁
    let Big (i : Iₐ) := orientPair i.1 ⁻¹' coarsePatch normal i.2.center i.2.scale (δ i.1)
    let Small (i : Iₐ) := orientPair i.1 ⁻¹' retainedPatch i.2.center i.2.scale κ
    have hScale (i : Iₐ) : 0 < i.2.scale := hs₀.trans_le i.2.scale_range.1
    have hSmallBig (i : Iₐ) : Small i ⊆ Big i :=
      preimage_mono ((retainedPatch_subset_coarsePatch (normal := normal)) _ (hScale i)
        (by linarith [hκδ i.1] : κ ≤ δ i.1))
    have hBig (i : Iₐ) : IsOpen (Big i) :=
      ((isOpen_coarsePatch (normal := normal)) _ _ _).preimage (continuous_orientPair i.1)
    have hSmall (i : Iₐ) : IsOpen (Small i) :=
      (isOpen_retainedPatch _ _ _).preimage (continuous_orientPair i.1)
    have hPatches (i : Iₐ) : ∃ K, ProductSolutionOn G₁ G₂ (Big i) K ∧
        EqOn K F (Big i ∩ lowerSidePairs normal η) ∧
        ∀ L : ℝ, 0 ≤ L → (∀ q ∈ lowerCross normal M η, (3/16 : ℝ)*d ≤ ‖q.1-q.2‖ → |F q| ≤ L) →
          ∀ q ∈ Small i, |K q| ≤ C*L := by
      rcases i with ⟨b,A⟩
      have hRet : retainedPatch A.center A.scale κ ⊆ retainedPatch A.center A.scale (δ b/2) := by
        apply Set.prod_mono (ball_subset_ball ?_) Subset.rfl
        exact mul_le_mul_of_nonneg_right (by linarith [hκδ b,hκ]) (hs₀.trans_le A.scale_range.1).le
      cases b
      · obtain ⟨K,hK,hKf,hKb⟩ := hp₁ A.center A.center_bounded A.center_planar
          A.scale A.scale_range η hηδ₁ F hF
        refine ⟨K,hK,hKf,fun L hL hb q hq => ?_⟩
        exact (hKb L hL (fun z hz hs => hb z hz (by dsimp [s₀] at hs; linarith)) q (hRet hq)).trans (mul_le_mul_of_nonneg_right
          ((le_max_left C₁ C₂).trans (le_max_right (1 : ℝ) (max C₁ C₂))) hL)
      · obtain ⟨K,hK,hKF,hKb⟩ := hp₂ A.center A.center_bounded A.center_planar A.scale A.scale_range
          η hηδ₂ (F ∘ Prod.swap) hFswap
        refine ⟨K ∘ Prod.swap,hK.swap,?_,?_⟩
        · intro q hq
          have hh := hKF (show q.swap ∈ coarsePatch normal A.center A.scale δ₂ ∩ lowerSidePairs normal η from
            ⟨hq.1,(lowerSidePairs_swap (normal := normal)) hq.2⟩)
          simpa only [Function.comp_apply,Prod.swap_swap] using hh
        · intro L hL hb q hq
          have hswap (z : (X dim) × (X dim)) (hz : z ∈ lowerCross normal M η)
              (hsep : (3/8 : ℝ)*s₀ ≤ ‖z.1-z.2‖) : |(F ∘ Prod.swap) z| ≤ L := by
            have hz' : z.swap ∈ lowerCross normal M η := by
              rw [← (swap_preimage_lowerCross (normal := normal)) M η] at hz
              exact hz
            simpa only [Function.comp_apply,Prod.fst_swap,Prod.snd_swap,norm_sub_rev] using hb z.swap hz' (by
              simpa only [Prod.fst_swap, Prod.snd_swap, norm_sub_rev] using
                (show (3/16 : ℝ)*d ≤ ‖z.1-z.2‖ by dsimp [s₀] at hsep; linarith))
          exact (hKb L hL hswap q.swap (hRet hq)).trans (mul_le_mul_of_nonneg_right
            ((le_max_right C₁ C₂).trans (le_max_right (1 : ℝ) (max C₁ C₂))) hL)
    choose K hK hKF hKB using hPatches
    have hCompat (i j : Iₐ) : EqOn (K i) (K j) (Small i ∩ Small j) := by
      intro q hq
      let U := Big i ∩ Big j
      let V := U ∩ lowerSidePairs normal η
      have hU : IsOpen U := (hBig i).inter (hBig j)
      have hV : IsOpen V := hU.inter ((isOpen_lowerSidePairs (normal := normal)) _)
      have hqU : q ∈ U := ⟨hSmallBig i hq.1,hSmallBig j hq.2⟩
      have hEq : EqOn (K i) (K j) V := fun z hz =>
        (hKF i ⟨hz.1.1,hz.2⟩).trans (hKF j ⟨hz.1.2,hz.2⟩).symm
      apply product_eq_at_of_interval_to_seed hU hV (A₁ := univ) (A₂ := univ)
        (by simp) hG₁ hG₂ ((hK i).mono inter_subset_left)
        ((hK j).mono inter_subset_right) hEq hqU
      obtain ⟨h,hh,hpath,hend⟩ := (exists_retained_overlap_lowering (normal := normal)) i.2.center_planar j.2.center_planar
        (hScale i) (hScale j) hκ hκcap (hκδ i.1) (hκδ j.1) hη
        (hηκ.trans (mul_le_mul_of_nonneg_left i.2.scale_range.1 hκ.le))
        (hηκ.trans (mul_le_mul_of_nonneg_left j.2.scale_range.1 hκ.le)) hq.1 hq.2
      have hpath' (t : ℝ) (ht : t ∈ uIcc 0 h) : lowerPairAt normal q t ∈ U :=
        hpath t (by simpa only [uIcc_of_le hh.le] using ht)
      exact ⟨0,h,lowerPairAt normal q,((continuous_lowerPairAt (normal := normal)) q).continuousOn,
        by simp [lowerPairAt],hpath',⟨hpath h ⟨hh.le,le_rfl⟩,hend⟩⟩
    let rooms : Option Iₐ → Set ((X dim) × (X dim))
      | none => lowerCross normal M η
      | some i => Small i
    let pieces : Option Iₐ → (X dim) × (X dim) → ℝ
      | none => F
      | some i => K i
    have hRooms (i : Option Iₐ) : IsOpen (rooms i) := by
      cases i
      · exact (isOpen_lowerCross (normal := normal)) _ _
      · exact hSmall _
    have hPieces (i : Option Iₐ) : ProductSolutionOn G₁ G₂ (rooms i) (pieces i) := by
      cases i
      · exact hF
      · exact (hK _).mono (hSmallBig _)
    have hBoth (i j : Option Iₐ) : EqOn (pieces i) (pieces j) (rooms i ∩ rooms j) := by
      cases i with
      | none =>
          cases j with
          | none => exact fun _ _ => rfl
          | some j =>
              intro z hz
              exact (hKF j ⟨hSmallBig j hz.2,(lowerCross_subset_lowerSidePairs (normal := normal)) M η hz.1⟩).symm
      | some i =>
          cases j with
          | none =>
              intro z hz
              exact hKF i ⟨hSmallBig i hz.1,(lowerCross_subset_lowerSidePairs (normal := normal)) M η hz.2⟩
          | some j => exact hCompat i j
    obtain ⟨G,hG,hAgree⟩ := exists_productSolution_iUnion rooms hRooms pieces hPieces hBoth
    have hLower : lowerCross normal M η ⊆ ⋃ i, rooms i := subset_iUnion rooms none
    refine ⟨⋃ i, rooms i,G,isOpen_iUnion hRooms,?_,hLower,hG,hAgree none,?_⟩
    · intro q hq
      rcases (coarseDomain_cover_lower_or_retained (normal := normal)) hd hκ hκcap hηd hM.le hq with hqLow | ⟨b,A,hqA⟩
      · exact hLower hqLow
      · exact mem_iUnion.mpr ⟨some (b,A),hqA⟩
    · intro L hL hb q hq
      rcases (coarseDomain_cover_lower_or_retained (normal := normal)) hd hκ hκcap hηd hM.le hq with hqLow | ⟨b,A,hqA⟩
      · have h := hAgree none hqLow
        change G q = F q at h
        rw [h]
        have hsep : (3/16 : ℝ)*d ≤ ‖q.1-q.2‖ := by linarith [hq.2.2.1]
        exact (hb q hqLow hsep).trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (max C₁ C₂)) hL)
      · have h := hAgree (some (b,A)) hqA
        change G q = K (b,A) q at h
        rw [h]
        exact hKB (b,A) L hL hb q hqA
  · refine ⟨0,le_rfl,Eventually.of_forall ?_⟩
    have hEmpty : coarseDomain normal B d (κ/4) ⊆ ∅ := by
      intro q hq
      have hnorm := norm_sub_le q.1 q.2
      have h₁ : ‖q.1‖ < B := hq.1
      have h₂ : ‖q.2‖ < B := hq.2.1
      have hs : d < ‖q.1-q.2‖ := hq.2.2.1
      exact (hdb (by linarith)).elim
    intro lam F hF
    exact ⟨lowerCross normal M η,F,(isOpen_lowerCross (normal := normal)) _ _,hEmpty.trans (empty_subset _),Subset.rfl,hF,
      fun _ _ => rfl,fun _ _ _ q hq => (hEmpty hq).elim⟩

set_option maxHeartbeats 1100000 in
/-- The two orientations glue to the actual bounded lower cross.
A fixed positive coarse slope works on every bounded positive
separation range. The comparison uses the larger patches along the
common downward interval. -/
theorem exists_glued_coarse_seed
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1) :
    ∃ c₀ > 0, ∀ B d ηcap : ℝ, 0 < B → 0 < d → 0 < ηcap →
      ∃ M η : ℝ, B < M ∧ 0 < η ∧ η ≤ ηcap ∧
        ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ F : (X dim) × (X dim) → ℝ,
          ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (lowerCross normal M η) F →
          ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ), IsOpen O ∧ coarseDomain normal B d c₀ ⊆ O ∧
            lowerCross normal M η ⊆ O ∧
            ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
            EqOn G F (lowerCross normal M η) := by
  obtain ⟨c₀,hc₀,h⟩ := (exists_glued_coarse_seed_with_bound (normal := normal)) hg₁ hg₂ h₁ h₂
  refine ⟨c₀,hc₀,fun B d η hB hd hη => ?_⟩
  obtain ⟨M,η',hM,hη',hηcap,_,_,h⟩ := h B d η hB hd hη
  exact ⟨M,η',hM,hη',hηcap,h.mono fun lam h F hF => by
    obtain ⟨O,G,hO,hCo,hLo,hG,hEq,_⟩ := h F hF
    exact ⟨O,G,hO,hCo,hLo,hG,hEq⟩⟩

end CalderonN.FixedTube
