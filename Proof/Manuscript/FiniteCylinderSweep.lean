module

public import Proof.Manuscript.CompactDataExtension
import Mathlib.Tactic

public section

open CalderonN Set Filter
open scoped Topology

namespace CalderonPaper

universe u

variable {dim : ℕ} {Z : Type u} [TopologicalSpace Z] {P : Type*}

set_option maxHeartbeats 1800000 in
/-- A finite continuation sweep with one reference neighborhood and
compact input budgets selected before the perturbation path. -/
theorem exists_compactDataExtension_across_cylinder
    (e : OpenPartialHomeomorph (X dim × X dim) (Z × ℝ))
    {B : Set Z} (hB : IsCompact B) {S : Set (X dim × X dim)} (hS : IsOpen S)
    {lo amin amax hi : ℝ} (hlo : lo < amin) (hab : amin ≤ amax) (hhi : amax < hi)
    (htarget : B ×ˢ Ioo lo hi ⊆ e.target)
    (htop : e.symm '' (B ×ˢ Ioo amax hi) ⊆ S)
    (hside : e.symm '' ((B \ interior B) ×ˢ Icc amin amax) ⊆ S)
    (solves : P → ℝ → Set (X dim × X dim) → (X dim × X dim → ℝ) → Prop)
    (hMono : ∀ path t {U V F}, V ⊆ U → solves path t U F → solves path t V F)
    (hInterval : ∀ path t {U V : Set (X dim × X dim)} {F G : X dim × X dim → ℝ},
      IsOpen U → IsOpen V → solves path t U F → solves path t U G → EqOn F G V →
      (∀ x ∈ U, ∃ (a b : ℝ) (f : ℝ → X dim × X dim),
        ContinuousOn f (uIcc a b) ∧ f a = x ∧ MapsTo f (uIcc a b) U ∧ f b ∈ V) →
      EqOn F G U)
    (hUnion : ∀ path t {ι : Type u} (U : ι → Set (X dim × X dim)) (hU : ∀ i, IsOpen (U i))
      (F : ι → X dim × X dim → ℝ), (∀ i, solves path t (U i) (F i)) →
      (∀ i j, EqOn (F i) (F j) (U i ∩ U j)) →
      ∃ G, solves path t (⋃ i, U i) G ∧ ∀ i, EqOn G (F i) (U i))
    (hLocal : ∀ a ∈ Icc amin amax, ∀ z ∈ interior B, e.symm (z, a) ∉ S →
      ∃ (B' : Set Z) (d b₀ : ℝ), IsOpen B' ∧ z ∈ B' ∧ B' ⊆ interior B ∧
        0 < d ∧ a < b₀ ∧ Ioo (a - d) (a + d) ⊆ Ioo lo hi ∧
        ∀ b ∈ Ico a b₀, CompactDataExtension solves (productAbove e B S b hi)
          (e.symm '' (B' ×ˢ Ioo (a - d) (a + d)))) :
    ∃ O : Set (X dim × X dim), IsOpen O ∧ S ∪ e.symm '' (B ×ˢ Icc amin amax) ⊆ O ∧
      O ⊆ productAbove e B S lo hi ∧ CompactDataExtension solves S O := by
  classical
  let A (a : ℝ) := productAbove e B S a hi
  have hOpen (a : ℝ) (ha : lo ≤ a) : IsOpen (A a) := isOpen_productAbove e hS ha htarget
  have hSeed (a : ℝ) : S ⊆ A a := subset_union_left
  let reached : Set ℝ := {a ∈ Icc amin amax | CompactDataExtension solves S (A a)}
  have htopSub : A amax ⊆ S := by
    rintro _ (hx | ⟨q, hq, rfl⟩)
    · exact hx
    · exact htop ⟨q, ⟨interior_subset hq.1, hq.2⟩, rfl⟩
  have htopR : amax ∈ reached :=
    ⟨⟨hab, le_rfl⟩, (CompactDataExtension.refl solves S).mono_right hMono htopSub⟩
  have hne : reached.Nonempty := ⟨amax, htopR⟩
  have hbd : BddBelow reached := ⟨amin, fun _ hx => hx.1.1⟩
  let a := sInf reached
  have ha : a ∈ Icc amin amax :=
    ⟨le_csInf hne (fun _ h => h.1.1), csInf_le hbd htopR⟩
  have hboxes (z : B) :
      ∃ (V : Set Z) (d b₀ : ℝ), IsOpen V ∧ z.val ∈ V ∧ 0 < d ∧ a < b₀ ∧
        V ×ˢ Ioo (a - d) (a + d) ⊆ e.target ∧
        (∀ b, ∀ q ∈ V ×ˢ Ioo (a - d) (a + d), b < q.2 → e.symm q ∈ A b) ∧
        ∀ b ∈ Ico a b₀, CompactDataExtension solves (A b)
          (e.symm '' (V ×ˢ Ioo (a - d) (a + d))) := by
    by_cases hz : e.symm (z.val, a) ∈ S
    · have hzT := htarget (show (z.val, a) ∈ B ×ˢ Ioo lo hi from
        ⟨z.property, hlo.trans_le ha.1, ha.2.trans_lt hhi⟩)
      have hN : {q : Z × ℝ | q ∈ e.target ∧ e.symm q ∈ S} ∈ 𝓝 (z.val, a) :=
        inter_mem (e.open_target.mem_nhds hzT)
          ((e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hzT)).preimage_mem_nhds
            (hS.mem_nhds hz))
      obtain ⟨V, d, hV, hzV, hd, hsub⟩ := exists_open_vertical_box_of_mem_nhds hN
      have hsub' : e.symm '' (V ×ˢ Ioo (a - d) (a + d)) ⊆ S := by
        rintro _ ⟨q, hq, rfl⟩
        exact (hsub hq).2
      refine ⟨V, d, a + d, hV, hzV, hd, lt_add_of_pos_right a hd,
        fun q hq => (hsub hq).1, ?_, ?_⟩
      · exact fun b q hq _ => hSeed b ((hsub hq).2)
      · exact fun b _ => (CompactDataExtension.refl solves (A b)).mono_right hMono
          (hsub'.trans (hSeed b))
    · have hzI : z.val ∈ interior B := by
        by_contra hh
        exact hz (hside ⟨(z.val, a), ⟨⟨z.property, hh⟩, ha⟩, rfl⟩)
      obtain ⟨V, d, b₀, hV, hzV, hVI, hd, hb₀, hstrip, hc⟩ := hLocal a ha z hzI hz
      refine ⟨V, d, b₀, hV, hzV, hd, hb₀, ?_, ?_, hc⟩
      · exact fun _ hq => htarget ⟨interior_subset (hVI hq.1), hstrip hq.2⟩
      · exact fun b q hq hqb => Or.inr ⟨q, ⟨hVI hq.1, hqb, (hstrip hq.2).2⟩, rfl⟩
  choose V d b₀ hV hzV hd hb₀ hVT hUpper hContinue using hboxes
  let w (z : B) := min (d z) (b₀ z - a)
  have hw (z : B) : 0 < w z := lt_min (hd z) (sub_pos.mpr (hb₀ z))
  have hCover : B ⊆ ⋃ z : B, V z := fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩
  obtain ⟨s, r, hr, hrs, hband⟩ := finite_vertical_cover hB V hV hCover w hw a
  obtain ⟨b, hb, hbr⟩ := exists_lt_of_csInf_lt hne (show a < a + r / 2 by linarith)
  have hab' : a ≤ b := csInf_le hbd hb
  let Q (i : s) : Set (Z × ℝ) := V i.val ×ˢ Ioo (a - d i.val) (a + d i.val)
  let W (i : s) := e.symm '' Q i
  have hW (i : s) : IsOpen (W i) :=
    e.isOpen_image_symm_of_subset_target ((hV i.val).prod isOpen_Ioo) (hVT i.val)
  have hWr (i : s) : r ≤ d i.val := (hrs i.val i.property).trans (min_le_left _ _)
  have hWb (i : s) : b < b₀ i.val := by
    have h := (hrs i.val i.property).trans (min_le_right (d i.val) (b₀ i.val - a))
    linarith
  have hlocal' (i : s) : CompactDataExtension solves (A b) (W i) :=
    hContinue i.val b ⟨hab', hWb i⟩
  have hbOpen := hOpen b (hlo.le.trans hb.1.1)
  have hGlue (path : P) (t : ℝ) (F : X dim × X dim → ℝ) (G : s → X dim × X dim → ℝ)
      (hF : solves path t (A b) F) (hG : ∀ i, solves path t (W i) (G i))
      (he : ∀ i, EqOn (G i) F (A b ∩ W i)) :
      ∃ H, solves path t (A b ∪ ⋃ i, W i) H ∧ EqOn H F (A b) ∧ ∀ i, EqOn H (G i) (W i) := by
    have hpair (i j : s) : EqOn (G i) (G j) (W i ∩ W j) := by
      let N := W i ∩ W j
      have hN := (hW i).inter (hW j)
      apply hInterval path t hN (hbOpen.inter hN)
        (hMono path t inter_subset_left (hG i)) (hMono path t inter_subset_right (hG j))
        (fun x hx => (he i ⟨hx.1, hx.2.1⟩).trans (he j ⟨hx.1, hx.2.2⟩).symm)
      rintro x ⟨⟨q, hq, rfl⟩, p, hp, hpq⟩
      have hp' : p = q := e.symm.injOn (hVT j.val hp) (hVT i.val hq) hpq
      subst p
      let c := a + r / 2
      have hc (k : s) : c ∈ Ioo (a - d k.val) (a + d k.val) := by
        constructor <;> dsimp [c] <;> linarith [hWr k, hd k.val]
      have interval_slice {l r : ℝ} (hq : q.2 ∈ Ioo l r) (hc : c ∈ Ioo l r)
          {t : ℝ} (ht : t ∈ uIcc q.2 c) : t ∈ Ioo l r := by
        rcases Set.mem_uIcc.mp ht with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
        · exact ⟨hq.1.trans_le hlo, hhi.trans_lt hc.2⟩
        · exact ⟨hc.1.trans_le hlo, hhi.trans_lt hq.2⟩
      have hseg (t : ℝ) (ht : t ∈ uIcc q.2 c) : (q.1, t) ∈ Q i ∩ Q j :=
        ⟨⟨hq.1, interval_slice hq.2 (hc i) ht⟩, ⟨hp.1, interval_slice hp.2 (hc j) ht⟩⟩
      have hUV t (ht : t ∈ uIcc q.2 c) : e.symm (q.1, t) ∈ N :=
        ⟨⟨_, (hseg t ht).1, rfl⟩, ⟨_, (hseg t ht).2, rfl⟩⟩
      refine ⟨q.2, c, fun t => e.symm (q.1, t),
        e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => hVT i.val (hseg t ht).1),
        rfl, hUV, hUpper i.val b _ ⟨hq.1, hc i⟩ hbr, hUV c right_mem_uIcc⟩
    let T (i : Option s) := i.elim (A b) W
    let L (i : Option s) := i.elim F G
    have hT (i : Option s) : IsOpen (T i) := by cases i with | none => exact hbOpen | some i => exact hW i
    have hL (i : Option s) : solves path t (T i) (L i) := by cases i with | none => exact hF | some i => exact hG i
    have heq (i j : Option s) : EqOn (L i) (L j) (T i ∩ T j) := by
      cases i <;> cases j
      · exact fun _ _ => rfl
      · exact fun _ hx => (he _ hx).symm
      · exact fun _ hx => he _ ⟨hx.2, hx.1⟩
      · exact hpair _ _
    obtain ⟨H, hH, hHL⟩ := hUnion path t T hT L hL heq
    refine ⟨H, hMono path t ?_ hH, hHL none, fun i => hHL (some i)⟩
    intro x hx
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨some i, hi⟩
  have hstage : CompactDataExtension solves (A b) (A b ∪ ⋃ i, W i) :=
    CompactDataExtension.glue W hbOpen hW hlocal' (fun path => .of_forall (hGlue path))
  let c := max ((lo + amin) / 2) (a - r / 2)
  have hlc : lo ≤ c := (by linarith : lo ≤ (lo + amin) / 2).trans (le_max_left _ _)
  have hca : c < a := max_lt (by linarith [ha.1]) (by linarith)
  have hcSub : A c ⊆ A b ∪ ⋃ i, W i := by
    rintro x (hx | ⟨q, hq, rfl⟩)
    · exact Or.inl (hSeed b hx)
    · by_cases hqb : b < q.2
      · exact Or.inl (Or.inr ⟨q, ⟨hq.1, hqb, hq.2.2⟩, rfl⟩)
      · have hl : a - r / 2 < q.2 := (le_max_right _ _).trans_lt hq.2.1
        have hu : q.2 ≤ b := le_of_not_gt hqb
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hband (show q ∈ B ×ˢ Ioo (a - r) (a + r) from
          ⟨interior_subset hq.1, by linarith, by linarith⟩))
        obtain ⟨his, hi⟩ := mem_iUnion.mp hi
        have hid : w i ≤ d i := min_le_left _ _
        exact Or.inr (mem_iUnion.mpr ⟨⟨i, his⟩, ⟨q, ⟨hi.1,
          (sub_le_sub_left hid _).trans_lt hi.2.1, hi.2.2.trans_le (add_le_add_right hid _)⟩, rfl⟩⟩)
  have hcR := hb.2.trans (hSeed b) (hstage.mono_right hMono hcSub)
  have haMin : a = amin := by
    by_contra hneq
    have hnew : max amin c < a := max_lt (lt_of_le_of_ne ha.1 (Ne.symm hneq)) hca
    have hnewR : max amin c ∈ reached :=
      ⟨⟨le_max_left _ _, hnew.le.trans ha.2⟩,
        hcR.mono_right hMono (productAbove_anti e B S (le_max_right _ _))⟩
    exact (not_lt_of_ge (csInf_le hbd hnewR)) hnew
  refine ⟨A c, hOpen c hlc, ?_, productAbove_anti e B S hlc, hcR⟩
  rintro x (hx | ⟨q, hq, rfl⟩)
  · exact hSeed c hx
  · by_cases hqI : q.1 ∈ interior B
    · exact Or.inr ⟨q, ⟨hqI, (haMin ▸ hca).trans_le hq.2.1, hq.2.2.trans_lt hhi⟩, rfl⟩
    · exact hSeed c (hside ⟨q, ⟨⟨hq.1, hqI⟩, hq.2⟩, rfl⟩)

end CalderonPaper
