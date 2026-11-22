module

public import Proof.Manuscript.FiniteHeightGeometry
import Mathlib.Tactic

public section

open Set Filter
open scoped Topology BigOperators

namespace CalderonPaper

variable {X P : Type*} [TopologicalSpace X]

/-- At each compact output set, one compact input set and one constant
work along every perturbation path through the reference problem. -/
@[expose] def CompactDataExtension
    (solves : P → ℝ → Set X → (X → ℝ) → Prop) (U V : Set X) : Prop :=
  ∀ K ⊆ V, IsCompact K → ∃ (L : Set X) (C : ℝ), IsCompact L ∧ L ⊆ U ∧ 0 ≤ C ∧
    ∀ path : P, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F : X → ℝ, solves path t U F →
      ∀ M : ℝ, 0 ≤ M → (∀ x ∈ L, |F x| ≤ M) →
      ∃ G : X → ℝ, solves path t V G ∧ EqOn G F (U ∩ V) ∧
        ∀ x ∈ K, |G x| ≤ C * M

theorem CompactDataExtension.refl
    (solves : P → ℝ → Set X → (X → ℝ) → Prop) (U : Set X) :
    CompactDataExtension solves U U := by
  intro K hK hKc
  refine ⟨K, 1, hKc, hK, zero_le_one, fun _ => .of_forall ?_⟩
  intro _ F hF M _ hM
  exact ⟨F, hF, fun _ _ => rfl, by simpa only [one_mul] using hM⟩

theorem CompactDataExtension.mono_right
    {solves : P → ℝ → Set X → (X → ℝ) → Prop}
    (mono : ∀ path t {U V F}, V ⊆ U → solves path t U F → solves path t V F)
    {U V W : Set X} (h : CompactDataExtension solves U V) (hWV : W ⊆ V) :
    CompactDataExtension solves U W := by
  intro K hK hKc
  obtain ⟨L, C, hL, hLU, hC, h⟩ := h K (hK.trans hWV) hKc
  refine ⟨L, C, hL, hLU, hC, fun path => (h path).mono ?_⟩
  intro t h F hF M hM hB
  obtain ⟨G, hG, he, hg⟩ := h F hF M hM hB
  exact ⟨G, mono path t hWV hG, he.mono (inter_subset_inter_right _ hWV), hg⟩

theorem CompactDataExtension.trans
    {solves : P → ℝ → Set X → (X → ℝ) → Prop} {S U V : Set X}
    (hSU : S ⊆ U) (h₁ : CompactDataExtension solves S U) (h₂ : CompactDataExtension solves U V) :
    CompactDataExtension solves S V := by
  intro K hKV hK
  obtain ⟨L, C₂, hL, hLU, hC₂, h₂⟩ := h₂ K hKV hK
  obtain ⟨T, C₁, hT, hTS, hC₁, h₁⟩ := h₁ L hLU hL
  refine ⟨T, C₂ * C₁, hT, hTS, mul_nonneg hC₂ hC₁, fun path => ?_⟩
  filter_upwards [h₁ path, h₂ path] with t hf hg F hF M hM hMC
  obtain ⟨G, hG, he, hGd⟩ := hf F hF M hM hMC
  obtain ⟨H, hH, hHe, hHc⟩ := hg G hG (C₁ * M) (mul_nonneg hC₁ hM) hGd
  refine ⟨H, hH, fun x hx => (hHe ⟨hSU hx.1, hx.2⟩).trans (he ⟨hx.1, hSU hx.1⟩), ?_⟩
  intro x hx
  simpa only [mul_assoc] using hHc x hx

/-- Glue finitely many local extensions with one compact input bound. -/
theorem CompactDataExtension.glue [LocallyCompactSpace X] [RegularSpace X]
    {solves : P → ℝ → Set X → (X → ℝ) → Prop} {U : Set X}
    {ι : Type*} [Fintype ι] (W : ι → Set X) (hU : IsOpen U) (hW : ∀ i, IsOpen (W i))
    (hLocal : ∀ i, CompactDataExtension solves U (W i))
    (hGlue : ∀ path : P, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ (F : X → ℝ) (G : ι → X → ℝ),
      solves path t U F → (∀ i, solves path t (W i) (G i)) →
      (∀ i, EqOn (G i) F (U ∩ W i)) →
      ∃ H : X → ℝ, solves path t (U ∪ ⋃ i, W i) H ∧ EqOn H F U ∧
        ∀ i, EqOn H (G i) (W i)) :
    CompactDataExtension solves U (U ∪ ⋃ i, W i) := by
  classical
  intro K hK hKc
  let W' (i : Option ι) := i.elim U W
  have hW' (i : Option ι) : IsOpen (W' i) := by cases i with | none => exact hU | some j => exact hW j
  have hcover : K ⊆ ⋃ i : Option ι, W' i := by
    intro x hx
    rcases hK hx with hx | hx
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨some i, hi⟩
  obtain ⟨K', hK'c, hK'sub, hK'⟩ := compact_subcover_inside hKc W' hW' hcover
  choose L C hLc hLU hC hL using fun i : ι => hLocal i (K' (some i)) (hK'sub (some i)) (hK'c (some i))
  let T := K' none ∪ ⋃ i, L i
  have hTc : IsCompact T := (hK'c none).union (isCompact_iUnion hLc)
  have hTU : T ⊆ U := union_subset (hK'sub none) (iUnion_subset hLU)
  let B := 1 + ∑ i, C i
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hC i)
  have hCB (i : ι) : C i ≤ B :=
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨T, B, hTc, hTU, zero_le_one.trans hB, fun path => ?_⟩
  have hL' := (eventually_all).mpr (fun i => hL i path)
  filter_upwards [hL', hGlue path] with t hl hg F hF M hM hMF
  have hproduce (i : ι) := hl i F hF M hM
    (fun x hx => hMF x (Or.inr (mem_iUnion.mpr ⟨i, hx⟩)))
  choose G hG hGF hGK using hproduce
  obtain ⟨H, hH, hHF, hHG⟩ := hg F G hF hG hGF
  refine ⟨H, hH, hHF.mono inter_subset_left, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hK' hx)
  cases i with
  | none =>
    rw [hHF (hK'sub none hi)]
    exact (hMF x (Or.inl hi)).trans (le_mul_of_one_le_left hM hB)
  | some i =>
    rw [hHG i (hK'sub (some i) hi)]
    exact (hGK i x hi).trans (mul_le_mul_of_nonneg_right (hCB i) hM)

end CalderonPaper
