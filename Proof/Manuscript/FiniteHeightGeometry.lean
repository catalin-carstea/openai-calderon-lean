module

public import Proof.CalderonN.ProductPropagation
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Tactic

public section

open CalderonN Set Filter
open scoped Topology

namespace CalderonPaper

variable {dim : ℕ} {Z : Type*} [TopologicalSpace Z]

/-- Open extensions shrink as the lower height increases. -/
theorem productAbove_anti
    (e : OpenPartialHomeomorph (X dim × X dim) (Z × ℝ))
    (B : Set Z) (S : Set (X dim × X dim)) {a b hi : ℝ} (hab : a ≤ b) :
    productAbove e B S b hi ⊆ productAbove e B S a hi := by
  apply union_subset_union_right
  exact image_mono (prod_mono Subset.rfl fun _ hz => ⟨hab.trans_lt hz.1, hz.2⟩)

theorem isOpen_productAbove
    (e : OpenPartialHomeomorph (X dim × X dim) (Z × ℝ))
    {B : Set Z} {S : Set (X dim × X dim)} (hS : IsOpen S)
    {lo a hi : ℝ} (hlo : lo ≤ a) (ht : B ×ˢ Ioo lo hi ⊆ e.target) :
    IsOpen (productAbove e B S a hi) :=
  hS.union (e.isOpen_image_symm_of_subset_target (isOpen_interior.prod isOpen_Ioo)
    (fun _ hz => ht ⟨interior_subset hz.1, hlo.trans_lt hz.2.1, hz.2.2⟩))

/-- A compact set strictly above a level remains above every sufficiently
nearby higher level, with the same seed included throughout. -/
theorem compact_subset_productAbove_near
    (e : OpenPartialHomeomorph (X dim × X dim) (Z × ℝ))
    {B : Set Z} {S L : Set (X dim × X dim)} (hS : IsOpen S) (hL : IsCompact L)
    {lo a hi : ℝ} (hlo : lo ≤ a) (hah : a < hi) (ht : B ×ˢ Ioo lo hi ⊆ e.target)
    (hLa : L ⊆ productAbove e B S a hi) :
    ∃ c ∈ Ioo a hi, ∀ b < c, L ⊆ productAbove e B S b hi := by
  classical
  let T := Ioo a hi
  let U (b : T) := productAbove e B S b.val hi
  have hU (b : T) : IsOpen (U b) :=
    isOpen_productAbove e hS (hlo.trans b.property.1.le) ht
  have hcover : L ⊆ ⋃ b : T, U b := by
    intro q hq
    rcases hLa hq with hs | ⟨z, hz, rfl⟩
    · have hm : (a + hi) / 2 ∈ T := ⟨by linarith, by linarith⟩
      exact mem_iUnion.mpr ⟨⟨_, hm⟩, Or.inl hs⟩
    · have hm : (a + z.2) / 2 ∈ T := ⟨by linarith [hz.2.1], by linarith [hz.2.1, hz.2.2]⟩
      have hb : (a + z.2) / 2 < z.2 := by linarith [hz.2.1]
      exact mem_iUnion.mpr ⟨⟨_, hm⟩, Or.inr ⟨z, ⟨hz.1, hb, hz.2.2⟩, rfl⟩⟩
  obtain ⟨s, hs⟩ := hL.elim_finite_subcover U hU hcover
  have hmin : ∀ t : Finset T, ∃ c ∈ T, ∀ b ∈ t, c ≤ (b : ℝ) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨(a + hi) / 2, ⟨by linarith, by linarith⟩, by simp⟩
    | @insert b t hbt ih =>
      obtain ⟨c, hc, hct⟩ := ih
      refine ⟨min c (b : ℝ), ⟨lt_min hc.1 b.property.1, (min_le_left _ _).trans_lt hc.2⟩, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hct q hq)
  obtain ⟨c, hc, hcs⟩ := hmin s
  refine ⟨c, hc, fun b hb q hq => ?_⟩
  obtain ⟨t, htq⟩ := mem_iUnion.mp (hs hq)
  obtain ⟨hts, htq⟩ := mem_iUnion.mp htq
  exact productAbove_anti e B S (hb.le.trans (hcs t hts)) htq

/-- A finite open box cover of a compact base also covers a uniform band. -/
theorem finite_vertical_cover
    {ι : Type*} {B : Set Z} (hB : IsCompact B) (U : ι → Set Z)
    (ho : ∀ i, IsOpen (U i)) (hcover : B ⊆ ⋃ i, U i)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (a : ℝ) :
    ∃ (s : Finset ι) (r : ℝ), 0 < r ∧ (∀ i ∈ s, r ≤ d i) ∧
      B ×ˢ Ioo (a - r) (a + r) ⊆ ⋃ i ∈ s, U i ×ˢ Ioo (a - d i) (a + d i) := by
  classical
  obtain ⟨s, hs⟩ := hB.elim_finite_subcover U ho hcover
  have hmin : ∀ t : Finset ι, ∃ r > 0, ∀ i ∈ t, r ≤ d i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert b t hbt ih =>
      obtain ⟨r, hr, hrt⟩ := ih
      refine ⟨min r (d b), lt_min hr (hd b), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hrt i hi)
  obtain ⟨r, hr, hrs⟩ := hmin s
  refine ⟨s, r, hr, hrs, ?_⟩
  intro q hq
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hq.1)
  obtain ⟨his, hi⟩ := mem_iUnion.mp hi
  have h := hrs i his
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨his, hi,
    (sub_le_sub_left h _).trans_lt hq.2.1, hq.2.2.trans_le (add_le_add_right h _)⟩⟩

/-- Reduce compact estimates on one open union to compact estimates in its pieces. -/
theorem compact_subcover_inside
    {X ι : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [RegularSpace X]
    {K : Set X} (hK : IsCompact K) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (L : ι → Set X), (∀ i, IsCompact (L i)) ∧ (∀ i, L i ⊆ U i) ∧ K ⊆ ⋃ i, L i := by
  classical
  have hlocal (x : K) : ∃ i : ι, ∃ V L : Set X, IsOpen V ∧ x.val ∈ V ∧
      V ⊆ L ∧ IsCompact L ∧ L ⊆ U i := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover x.property)
    obtain ⟨L, hLc, hLn, hLU⟩ :=
      exists_compact_subset (hU i) hi
    exact ⟨i, interior L, L, isOpen_interior, hLn, interior_subset, hLc, hLU⟩
  choose i V L hV hxV hVL hL hLU using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let A (j : ι) := ⋃ x ∈ s.filter (fun x => i x = j), L x
  refine ⟨A, fun j => (s.filter (fun x => i x = j)).finite_toSet.isCompact_biUnion
    (fun x _ => hL x), ?_, ?_⟩
  · intro j x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    obtain ⟨hqs, hqx⟩ := mem_iUnion.mp hq
    simpa only [(Finset.mem_filter.mp hqs).2] using hLU q hqx
  · intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hqs, hqx⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨i q, mem_iUnion.mpr ⟨q, mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨hqs, rfl⟩, hVL q hqx⟩⟩⟩

end CalderonPaper
