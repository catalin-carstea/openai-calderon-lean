module

public import Proof.CalderonN.ProductGluing
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

import Mathlib.Tactic.Linarith

@[expose] public section

open Set

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem exists_common_box_width {Z ι : Type*} [TopologicalSpace Z]
    {K : Set Z} (hK : IsCompact K) (B : ι → Set Z) (hB : ∀ i, IsOpen (B i))
    (hcover : K ⊆ ⋃ i, B i) (d : ι → ℝ) (hd : ∀ i, 0 < d i) (a : ℝ) :
    ∃ r > 0, K ×ˢ Ioo (a-r) (a+r) ⊆ ⋃ i, B i ×ˢ Ioo (a-d i) (a+d i) := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover B hB hcover
  have hwidth : ∀ t : Finset ι, ∃ r > 0, ∀ i ∈ t, r ≤ d i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i t hit ih =>
      obtain ⟨r, hr, hle⟩ := ih
      refine ⟨min r (d i), lt_min hr (hd i), fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle j hj)
  obtain ⟨r, hr, hle⟩ := hwidth s
  refine ⟨r, hr, ?_⟩
  rintro ⟨z,t⟩ ⟨hz,ht⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hz)
  obtain ⟨his, hzB⟩ := mem_iUnion.mp hi
  have h := hle i his
  exact mem_iUnion.mpr ⟨i,hzB,(sub_le_sub_left h _).trans_lt ht.1, ht.2.trans_le (add_le_add_right h _)⟩

/-- A finite family of local continuations across one compact level
glues to a continuation with positive common width. Every overlap is
identified by a vertical segment in the same chart. -/
theorem exists_productSolution_across_compact_level
    {Z ι : Type*} [TopologicalSpace Z] (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ))
    {K : Set Z} (hK : IsCompact K) (a : ℝ) (B : ι → Set Z) (d : ι → ℝ)
    (hB : ∀ i, IsOpen (B i)) (hd : ∀ i, 0 < d i) (hcover : K ⊆ ⋃ i, B i)
    (htarget : ∀ i, B i ×ˢ Ioo (a-d i) (a+d i) ⊆ e.target)
    {Ω₁ Ω₂ : Set (X dim)} {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric Ω₁ g₁) (hg₂ : SmoothMetric Ω₂ g₂)
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O) (F : (X dim) × (X dim) → ℝ)
    (hF : ProductSolutionOn g₁ g₂ O F)
    (G : ι → (X dim) × (X dim) → ℝ)
    (hlocal : ∀ i, ProductSolutionOn g₁ g₂ (e.symm '' (B i ×ˢ Ioo (a-d i) (a+d i))) (G i))
    (hcoord : ∀ i, e.symm '' (B i ×ˢ Ioo (a-d i) (a+d i)) ⊆ Ω₁ ×ˢ Ω₂)
    (hup : ∀ i, ∀ q ∈ B i ×ˢ Ioo (a-d i) (a+d i), a < q.2 → e.symm q ∈ O)
    (hagree : ∀ i, EqOn (G i) F ((e.symm '' (B i ×ˢ Ioo (a-d i) (a+d i))) ∩ O)) :
    ∃ r > 0, ∃ H : (X dim) × (X dim) → ℝ,
      ProductSolutionOn g₁ g₂ (O ∪ e.symm '' (K ×ˢ Ioo (a-r) (a+r))) H ∧ EqOn H F O := by
  let C (i : ι) := B i ×ˢ Ioo (a-d i) (a+d i)
  let U (i : ι) := e.symm '' C i
  have hU (i : ι) : IsOpen (U i) :=
    e.isOpen_image_symm_of_subset_target ((hB i).prod isOpen_Ioo) (htarget i)
  have hcompat (i j : ι) : EqOn (G i) (G j) (U i ∩ U j) := by
    let V := (U i ∩ U j) ∩ O
    apply product_eqOn_of_interval_to_seed ((hU i).inter (hU j)) (((hU i).inter (hU j)).inter hO)
      (inter_subset_left.trans (hcoord i)) hg₁ hg₂
      ((hlocal i).mono inter_subset_left) ((hlocal j).mono inter_subset_right)
      (fun z hz => (hagree i ⟨hz.1.1,hz.2⟩).trans (hagree j ⟨hz.1.2,hz.2⟩).symm)
    intro z hz
    obtain ⟨p,hp,rfl⟩ := hz.1
    obtain ⟨q,hq,heq⟩ := hz.2
    have hqp : q = p := e.symm.injOn (htarget j hq) (htarget i hp) heq
    rw [hqp] at hq
    obtain ⟨b,hb,hseg⟩ := exists_vertical_overlap_segment (B i) (B j) a (d i) (d j)
      (hd i) (hd j) p ⟨hp,hq⟩
    let f (t : ℝ) := e.symm (p.1,t)
    have htgt : MapsTo (fun t : ℝ => (p.1,t)) (uIcc p.2 b) e.target :=
      fun t ht => htarget i (hseg t ht).1
    have hPath : ContinuousOn f (uIcc p.2 b) :=
      e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn htgt
    have hin : MapsTo f (uIcc p.2 b) (U i ∩ U j) := fun t ht =>
      ⟨⟨(p.1,t),(hseg t ht).1,rfl⟩,⟨(p.1,t),(hseg t ht).2,rfl⟩⟩
    exact ⟨p.2,b,f,hPath,rfl,hin,hin right_mem_uIcc,hup i (p.1,b) (hseg b right_mem_uIcc).1 hb⟩
  obtain ⟨r,hr,hwidth⟩ := exists_common_box_width hK B hB hcover d hd a
  let U' : Option ι → Set ((X dim) × (X dim)) := fun j => j.elim O U
  let G' : Option ι → (X dim) × (X dim) → ℝ := fun j => j.elim F G
  have hU' (j : Option ι) : IsOpen (U' j) := by cases j with | none => exact hO | some i => exact hU i
  have hG' (j : Option ι) : ProductSolutionOn g₁ g₂ (U' j) (G' j) := by
    cases j with | none => exact hF | some i => exact hlocal i
  have hcompat' (i j : Option ι) : EqOn (G' i) (G' j) (U' i ∩ U' j) := by
    cases i <;> cases j
    · exact fun _ _ => rfl
    · exact fun _ hx => (hagree _ ⟨hx.2,hx.1⟩).symm
    · exact hagree _
    · exact hcompat _ _
  obtain ⟨H,hH,heq⟩ := exists_productSolution_iUnion U' hU' G' hG' hcompat'
  refine ⟨r,hr,H,hH.mono ?_,heq none⟩
  rintro z (hz | ⟨q,hq,rfl⟩)
  · exact mem_iUnion.mpr ⟨none,hz⟩
  · obtain ⟨i,hi⟩ := mem_iUnion.mp (hwidth hq)
    exact mem_iUnion.mpr ⟨some i,⟨q,hi,rfl⟩⟩

end CalderonN
