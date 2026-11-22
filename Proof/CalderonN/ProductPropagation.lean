module

public import Proof.CalderonN.VerticalGluing

import Mathlib.Tactic

@[expose] public section

open Set Filter
open scoped Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem exists_open_vertical_box_of_mem_nhds {Z : Type*} [TopologicalSpace Z]
    {E : Set (Z × ℝ)} {z : Z} {a : ℝ} (hE : E ∈ 𝓝 (z,a)) :
    ∃ (B : Set Z) (d : ℝ), IsOpen B ∧ z ∈ B ∧ 0 < d ∧
      B ×ˢ Ioo (a-d) (a+d) ⊆ E := by
  obtain ⟨U,hU,J,hI,hsub⟩ := mem_nhds_prod_iff.mp hE
  obtain ⟨d,hd,hD⟩ := Metric.mem_nhds_iff.mp hI
  have hdI : Ioo (a-d) (a+d) ⊆ J := by
    intro t ht
    apply hD
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨interior U,d,isOpen_interior,mem_interior_iff_mem_nhds.mpr hU,hd,
    (Set.prod_mono interior_subset hdI).trans hsub⟩

/-- The already available domain at height `a`, together with the prescribed seed. -/
@[expose] def productAbove {Z : Type*} [TopologicalSpace Z]
    (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ)) (K : Set Z) (S : Set ((X dim) × (X dim)))
    (a upper : ℝ) : Set ((X dim) × (X dim)) := S ∪ e.symm '' (interior K ×ˢ Ioo a upper)

private theorem productAbove_isOpen {Z : Type*} [TopologicalSpace Z]
    (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ)) {K : Set Z} {S : Set ((X dim) × (X dim))}
    (hS : IsOpen S) {lo upper a : ℝ} (hla : lo ≤ a)
    (htarget : K ×ˢ Ioo lo upper ⊆ e.target) : IsOpen (productAbove e K S a upper) :=
  hS.union (e.isOpen_image_symm_of_subset_target (isOpen_interior.prod isOpen_Ioo)
    (fun _ h => htarget ⟨interior_subset h.1,hla.trans_lt h.2.1,h.2.2⟩))

private theorem productAbove_eqOn {Z : Type*} [TopologicalSpace Z]
    (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ)) {K : Set Z} {S : Set ((X dim) × (X dim))}
    (hS : IsOpen S) {lo upper top a b : ℝ} (hla : lo ≤ a) (hlb : lo ≤ b)
    (htu : top < upper) (htarget : K ×ˢ Ioo lo upper ⊆ e.target)
    (htop : e.symm '' (K ×ˢ Ioo top upper) ⊆ S)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {F G : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ (productAbove e K S a upper) F)
    (hG : ProductSolutionOn g₁ g₂ (productAbove e K S b upper) G) (heq : EqOn F G S) :
    EqOn F G (productAbove e K S a upper ∩ productAbove e K S b upper) := by
  let U := productAbove e K S a upper ∩ productAbove e K S b upper
  apply product_eqOn_of_interval_to_seed
    ((productAbove_isOpen e hS hla htarget).inter (productAbove_isOpen e hS hlb htarget))
    hS (by simp) hg₁ hg₂ (hF.mono inter_subset_left) (hG.mono inter_subset_right) heq
  intro x hx
  by_cases hxS : x ∈ S
  · exact ⟨0,0,fun _ => x,continuousOn_const,rfl,fun _ _ => hx,hxS⟩
  obtain ⟨q,hq,rfl⟩ := hx.1.resolve_left hxS
  obtain ⟨q',hq',he⟩ := hx.2.resolve_left hxS
  have hqa := htarget ⟨interior_subset hq.1,hla.trans_lt hq.2.1,hq.2.2⟩
  have hqb := htarget ⟨interior_subset hq'.1,hlb.trans_lt hq'.2.1,hq'.2.2⟩
  have heq' := e.symm.injOn hqb hqa he
  subst q'
  let c := (max q.2 top + upper) / 2
  have hm := max_lt hq.2.2 htu
  have hqc : q.2 < c := by dsimp only [c]; linarith [le_max_left q.2 top]
  have htc : top < c := by dsimp only [c]; linarith [le_max_right q.2 top]
  have hcu : c < upper := by dsimp only [c]; linarith
  let f (s : ℝ) := e.symm (q.1,s)
  have hin : MapsTo (fun s : ℝ => (q.1,s)) (uIcc q.2 c) e.target := by
    intro s hs
    rw [uIcc_of_le hqc.le] at hs
    exact htarget ⟨interior_subset hq.1,(hla.trans_lt hq.2.1).trans_le hs.1,hs.2.trans_lt hcu⟩
  refine ⟨q.2,c,f,e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn hin,
    rfl,?_,htop ⟨(q.1,c),⟨interior_subset hq.1,htc,hcu⟩,rfl⟩⟩
  intro s hs
  rw [uIcc_of_le hqc.le] at hs
  exact ⟨Or.inr ⟨(q.1,s),⟨hq.1,hq.2.1.trans_le hs.1,hs.2.trans_lt hcu⟩,rfl⟩,
    Or.inr ⟨(q.1,s),⟨hq'.1,hq'.2.1.trans_le hs.1,hs.2.trans_lt hcu⟩,rfl⟩⟩

private theorem product_eqOn_box_of_upper {Z : Type*} [TopologicalSpace Z]
    (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ)) {K B : Set Z} {S : Set ((X dim) × (X dim))}
    (hS : IsOpen S) (hB : IsOpen B) (hBK : B ⊆ interior K)
    {lo upper a d : ℝ} (hla : lo ≤ a) (hd : 0 < d)
    (hstrip : Ioo (a-d) (a+d) ⊆ Ioo lo upper)
    (htarget : K ×ˢ Ioo lo upper ⊆ e.target)
    (hup : ∀ z ∈ K, ∀ s t : ℝ, s ∈ Ioo lo upper → t ∈ Ioo lo upper →
      s ≤ t → e.symm (z,s) ∈ S → e.symm (z,t) ∈ S)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {F G : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ (productAbove e K S a upper) F)
    (hG : ProductSolutionOn g₁ g₂ (e.symm '' (B ×ˢ Ioo (a-d) (a+d))) G)
    (heq : EqOn G F (e.symm '' (B ×ˢ Ioo a (a+d)))) :
    EqOn G F ((e.symm '' (B ×ˢ Ioo (a-d) (a+d))) ∩ productAbove e K S a upper) := by
  let C := B ×ˢ Ioo (a-d) (a+d)
  let U := e.symm '' C
  let V := e.symm '' (B ×ˢ Ioo a (a+d))
  have hC : C ⊆ e.target := fun _ h => htarget ⟨interior_subset (hBK h.1),hstrip h.2⟩
  have hV : B ×ˢ Ioo a (a+d) ⊆ C := fun q h =>
    ⟨h.1,(sub_lt_self a hd).trans h.2.1,h.2.2⟩
  apply product_eqOn_of_interval_to_seed
    ((e.isOpen_image_symm_of_subset_target (hB.prod isOpen_Ioo) hC).inter
      (productAbove_isOpen e hS hla htarget))
    (e.isOpen_image_symm_of_subset_target (hB.prod isOpen_Ioo) (hV.trans hC))
    (by simp) hg₁ hg₂ (hG.mono inter_subset_left) (hF.mono inter_subset_right) heq
  rintro x ⟨⟨q,hq,rfl⟩,hO⟩
  by_cases hqa : a < q.2
  · exact ⟨0,0,fun _ => e.symm q,continuousOn_const,rfl,
      fun _ _ => ⟨⟨q,hq,rfl⟩,hO⟩,⟨q,⟨hq.1,hqa,hq.2.2⟩,rfl⟩⟩
  have hqS : e.symm q ∈ S := by
    rcases hO with h | ⟨p,hp,he⟩
    · exact h
    · have hpt := htarget ⟨interior_subset hp.1,hla.trans_lt hp.2.1,hp.2.2⟩
      have heq' := e.symm.injOn hpt (hC hq) he
      subst p
      exact (hqa hp.2.1).elim
  let b := a + d / 2
  have hb : a < b := by dsimp only [b]; linarith
  have hb' : b < a + d := by dsimp only [b]; linarith
  have hqb : q.2 ≤ b := (le_of_not_gt hqa).trans hb.le
  have hseg (t : ℝ) (ht : t ∈ uIcc q.2 b) : (q.1,t) ∈ C := by
    rw [uIcc_of_le hqb] at ht
    exact ⟨hq.1,hq.2.1.trans_le ht.1,ht.2.trans_lt hb'⟩
  let f (t : ℝ) := e.symm (q.1,t)
  refine ⟨q.2,b,f,e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun t ht => hC (hseg t ht)),rfl,?_,⟨(q.1,b),⟨hq.1,hb,hb'⟩,rfl⟩⟩
  intro t ht
  have hs := hseg t ht
  have hqt : q.2 ≤ t := by
    rw [uIcc_of_le hqb] at ht
    exact ht.1
  exact ⟨⟨(q.1,t),hs,rfl⟩,Or.inl (hup q.1 (interior_subset (hBK hq.1)) q.2 t
    (hstrip hq.2) (hstrip hs.2) hqt hqS)⟩

set_option maxHeartbeats 1200000 in
/-- Qualitative propagation across a compact cylinder. The local continuation
at each unseeded point uses a solution on the open region strictly above its
level. The union at the infimum supplies this open region, and every overlap
agrees with the seed by an actual upward interval path. -/
theorem exists_productSolution_across_compact_cylinder
    {Z : Type*} [TopologicalSpace Z] (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ))
    {K : Set Z} (hK : IsCompact K) {S : Set ((X dim) × (X dim))} (hS : IsOpen S)
    {lo amin amax upper : ℝ} (hlo : lo < amin) (hab : amin ≤ amax) (hhi : amax < upper)
    (htarget : K ×ˢ Ioo lo upper ⊆ e.target)
    (habove : e.symm '' (K ×ˢ Ioo amax upper) ⊆ S)
    (hside : e.symm '' ((K \ interior K) ×ˢ Icc amin amax) ⊆ S)
    (hup : ∀ z ∈ K, ∀ s t : ℝ, s ∈ Ioo lo upper → t ∈ Ioo lo upper →
      s ≤ t → e.symm (z,s) ∈ S → e.symm (z,t) ∈ S)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (Fseed : (X dim) × (X dim) → ℝ) (hseed : ProductSolutionOn g₁ g₂ S Fseed)
    (hlocal : ∀ a ∈ Icc amin amax, ∀ F, ProductSolutionOn g₁ g₂ (productAbove e K S a upper) F →
      EqOn F Fseed S → ∀ z ∈ interior K, e.symm (z,a) ∉ S →
      ∃ (B : Set Z) (d : ℝ) (G : (X dim) × (X dim) → ℝ),
        IsOpen B ∧ z ∈ B ∧ B ⊆ interior K ∧ 0 < d ∧ Ioo (a-d) (a+d) ⊆ Ioo lo upper ∧
        ProductSolutionOn g₁ g₂ (e.symm '' (B ×ˢ Ioo (a-d) (a+d))) G ∧
        EqOn G F (e.symm '' (B ×ˢ Ioo a (a+d)))) :
    ∃ O : Set ((X dim) × (X dim)), IsOpen O ∧ S ∪ e.symm '' (K ×ˢ Icc amin amax) ⊆ O ∧
      ∃ G, ProductSolutionOn g₁ g₂ O G ∧ EqOn G Fseed S := by
  classical
  let A (a : ℝ) := productAbove e K S a upper
  have hA (a : ℝ) (ha : lo ≤ a) : IsOpen (A a) := productAbove_isOpen e hS ha htarget
  have hSsub' (a : ℝ) : S ⊆ A a := subset_union_left
  let Reached : Set ℝ := {a ∈ Icc amin amax | ∃ F, ProductSolutionOn g₁ g₂ (A a) F ∧ EqOn F Fseed S}
  have htopR : amax ∈ Reached := by
    have ht : A amax ⊆ S := by
      rintro x (hx | ⟨q,hq,rfl⟩)
      · exact hx
      · exact habove ⟨q,⟨interior_subset hq.1,hq.2⟩,rfl⟩
    exact ⟨⟨hab,le_rfl⟩,Fseed,hseed.mono ht,fun _ _ => rfl⟩
  have hne : Reached.Nonempty := ⟨amax,htopR⟩
  have hbd : BddBelow Reached := ⟨amin,fun _ hr => hr.1.1⟩
  let a := sInf Reached
  have ha : a ∈ Icc amin amax :=
    ⟨le_csInf hne (fun _ hr => hr.1.1),csInf_le hbd htopR⟩
  have hsol (b : Reached) : ∃ F, ProductSolutionOn g₁ g₂ (A b) F ∧ EqOn F Fseed S :=
    b.property.2
  choose F hF heq using hsol
  have hcompat (b c : Reached) : EqOn (F b) (F c) (A b ∩ A c) :=
    productAbove_eqOn e hS (hlo.le.trans b.property.1.1) (hlo.le.trans c.property.1.1)
      hhi htarget habove hg₁ hg₂ (hF b) (hF c)
      (fun _ hx => (heq b hx).trans (heq c hx).symm)
  obtain ⟨G,hG,hGagree⟩ := exists_productSolution_iUnion (fun b : Reached => A b)
    (fun b => hA b (hlo.le.trans b.property.1.1)) F hF hcompat
  have haboveG : ProductSolutionOn g₁ g₂ (A a) G := by
    apply hG.mono
    rintro x (hx | ⟨q,hq,rfl⟩)
    · exact mem_iUnion.mpr ⟨⟨amax,htopR⟩,Or.inl hx⟩
    · obtain ⟨b,hb,hbq⟩ := exists_lt_of_csInf_lt hne hq.2.1
      exact mem_iUnion.mpr ⟨⟨b,hb⟩,Or.inr ⟨q,⟨hq.1,hbq,hq.2.2⟩,rfl⟩⟩
  have heG : EqOn G Fseed S := fun x hx =>
    (hGagree ⟨amax,htopR⟩ (hSsub' _ hx)).trans (heq ⟨amax,htopR⟩ hx)
  have boxes (z : K) : ∃ (B : Set Z) (d : ℝ) (H : (X dim) × (X dim) → ℝ), IsOpen B ∧ (z : Z) ∈ B ∧
      0 < d ∧ B ×ˢ Ioo (a-d) (a+d) ⊆ e.target ∧
      ProductSolutionOn g₁ g₂ (e.symm '' (B ×ˢ Ioo (a-d) (a+d))) H ∧
      e.symm '' (B ×ˢ Ioo a (a+d)) ⊆ A a ∧
      EqOn H G ((e.symm '' (B ×ˢ Ioo (a-d) (a+d))) ∩ A a) := by
    by_cases hz : e.symm ((z : Z),a) ∈ S
    · have hT : ((z : Z),a) ∈ e.target :=
        htarget ⟨z.property,hlo.trans_le ha.1,ha.2.trans_lt hhi⟩
      have hN : {p : Z × ℝ | p ∈ e.target ∧ e.symm p ∈ S} ∈ 𝓝 ((z : Z),a) :=
        inter_mem (e.open_target.mem_nhds hT)
          ((e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hT)).preimage_mem_nhds (hS.mem_nhds hz))
      obtain ⟨B,d,hB,hzB,hd,hs⟩ := exists_open_vertical_box_of_mem_nhds hN
      refine ⟨B,d,Fseed,hB,hzB,hd,fun q h => (hs h).1, hseed.mono ?_, ?_, ?_⟩
      · rintro _ ⟨q,hq,rfl⟩
        exact (hs hq).2
      · rintro _ ⟨q,hq,rfl⟩
        exact Or.inl (hs ⟨hq.1,(sub_lt_self a hd).trans hq.2.1,hq.2.2⟩).2
      · rintro _ ⟨⟨q,hq,rfl⟩,-⟩
        exact (heG (hs hq).2).symm
    · have hzK : (z : Z) ∈ interior K := by
        by_contra hn
        exact hz (hside ⟨((z : Z),a),⟨⟨z.property,hn⟩,ha⟩,rfl⟩)
      obtain ⟨B,d,H,hB,hzB,hBK,hd,hstrip,hH,hHG⟩ := hlocal a ha G haboveG heG z hzK hz
      refine ⟨B,d,H,hB,hzB,hd,fun _ hq => htarget ⟨interior_subset (hBK hq.1),hstrip hq.2⟩,hH,
        ?_,product_eqOn_box_of_upper e hS hB hBK (hlo.le.trans ha.1) hd hstrip htarget hup
          hg₁ hg₂ haboveG hH hHG⟩
      rintro _ ⟨q,hq,rfl⟩
      have hs := hstrip ⟨(sub_lt_self a hd).trans hq.2.1,hq.2.2⟩
      exact Or.inr ⟨q,⟨hBK hq.1,hq.2.1,hs.2⟩,rfl⟩
  choose B d H hB hzB hd htargetB hH hupper hHG using boxes
  have hcover : K ⊆ ⋃ z : K, B z := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzB ⟨z,hz⟩⟩
  obtain ⟨r,hr,J,hJ,hJG⟩ := exists_productSolution_across_compact_level e hK a B d hB hd hcover
    htargetB hg₁ hg₂ (hA a (hlo.le.trans ha.1)) G haboveG H hH (fun _ => by simp)
    (fun i q hq hqa => hupper i ⟨q,⟨hq.1,hqa,hq.2.2⟩,rfl⟩) hHG
  have heJ : EqOn J Fseed S := fun x hx => (hJG (hSsub' a hx)).trans (heG hx)
  have hdown : A (max amin (a-r/2)) ⊆ A a ∪ e.symm '' (K ×ˢ Ioo (a-r) (a+r)) := by
    rintro _ (hx | ⟨q,hq,rfl⟩)
    · exact Or.inl (Or.inl hx)
    · by_cases hqa : a < q.2
      · exact Or.inl (Or.inr ⟨q,⟨hq.1,hqa,hq.2.2⟩,rfl⟩)
      · have hf := (le_max_right amin (a-r/2)).trans_lt hq.2.1
        exact Or.inr ⟨q,⟨interior_subset hq.1,by linarith,by linarith [le_of_not_gt hqa]⟩,rfl⟩
  have hamin : a = amin := by
    by_contra hne'
    have hnew : max amin (a-r/2) < a := max_lt (lt_of_le_of_ne ha.1 (Ne.symm hne')) (by linarith)
    have hr' : max amin (a-r/2) ∈ Reached :=
      ⟨⟨le_max_left _ _,hnew.le.trans ha.2⟩,J,hJ.mono hdown,heJ⟩
    exact (not_lt_of_ge (csInf_le hbd hr')) hnew
  let b := max ((lo+amin)/2) (amin-r/2)
  have hb : lo ≤ b := (by linarith : lo ≤ (lo+amin)/2).trans (le_max_left _ _)
  have hba : b < amin := max_lt (by linarith) (by linarith)
  have hsub : A b ⊆ A a ∪ e.symm '' (K ×ˢ Ioo (a-r) (a+r)) := by
    rintro _ (hx | ⟨q,hq,rfl⟩)
    · exact Or.inl (Or.inl hx)
    · by_cases hqa : a < q.2
      · exact Or.inl (Or.inr ⟨q,⟨hq.1,hqa,hq.2.2⟩,rfl⟩)
      · have hf := (le_max_right ((lo+amin)/2) (amin-r/2)).trans_lt hq.2.1
        exact Or.inr ⟨q,⟨interior_subset hq.1,by linarith,by linarith [le_of_not_gt hqa]⟩,rfl⟩
  refine ⟨A b,hA b hb,?_,J,hJ.mono hsub,heJ⟩
  rintro x (hx | ⟨q,hq,rfl⟩)
  · exact Or.inl hx
  · by_cases hi : q.1 ∈ interior K
    · exact Or.inr ⟨q,⟨hi,hba.trans_le hq.2.1,hq.2.2.trans_lt hhi⟩,rfl⟩
    · exact Or.inl (hside ⟨q,⟨⟨hq.1,hi⟩,hq.2⟩,rfl⟩)

end CalderonN
