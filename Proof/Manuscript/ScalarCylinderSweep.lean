module

public import Proof.Manuscript.FiniteCylinderSweep
public import Proof.Manuscript.CompactSweepEstimates
public import Proof.Manuscript.ScalarProductGluing

public section

open CalderonN Set Filter
open CalderonPaper.ScalarElliptic
open scoped Topology

namespace CalderonPaper

variable {n : ℕ} [NeZero n]

/-- An admissible perturbation of a fixed pair of reference operators. -/
structure ScalarSweepPath (D₁ D₂ : Set (X n)) (L₁₀ L₂₀ : ScalarElliptic n) where
  left : ℝ → ScalarElliptic n
  right : ℝ → ScalarElliptic n
  smoothLeft : ScalarElliptic.SmoothFamilyOn left D₁
  smoothRight : ScalarElliptic.SmoothFamilyOn right D₂
  referenceLeft : left 0 = L₁₀
  referenceRight : right 0 = L₂₀

@[expose] def ScalarSweepPath.solves {D₁ D₂ : Set (X n)} {L₁₀ L₂₀ : ScalarElliptic n}
    (path : ScalarSweepPath D₁ D₂ L₁₀ L₂₀) (t : ℝ) (O : Set (X n × X n))
    (F : X n × X n → ℝ) : Prop :=
  O ⊆ D₁ ×ˢ D₂ ∧ (path.left t).ProductSolvesOn (path.right t) O F

/-- The exact analytic premises needed to propagate scalar product solutions
through a fixed cylinder. The output has the quantifier order of Lemma 3.4. -/
theorem scalar_cylinder_sweep_of_local_extensions
    {Z : Type*} [TopologicalSpace Z]
    (e : OpenPartialHomeomorph ((X n) × (X n)) (Z × ℝ))
    {B : Set Z} (hB : IsCompact B) {lo amin amax hi : ℝ}
    (hlo : lo < amin) (hab : amin ≤ amax) (hhi : amax < hi)
    (htarget : B ×ˢ Ioo lo hi ⊆ e.target)
    {D₁ D₂ : Set (X n)} (hChartD : e.symm '' (B ×ˢ Ioo lo hi) ⊆ D₁ ×ˢ D₂)
    {S : Set (X n × X n)} (hS : IsOpen S) (hSD : S ⊆ D₁ ×ˢ D₂)
    (htop : e.symm '' (B ×ˢ Ico amax hi) ⊆ S)
    (hside : e.symm '' ((B \ interior B) ×ˢ Icc amin amax) ⊆ S)
    (L₁₀ L₂₀ : ScalarElliptic n)
    (hLocal : ∀ a ∈ Icc amin amax, ∀ z ∈ interior B, e.symm (z, a) ∉ S →
      ∃ (B' : Set Z) (d b₀ : ℝ), IsOpen B' ∧ z ∈ B' ∧ B' ⊆ interior B ∧
        0 < d ∧ a < b₀ ∧ Ioo (a - d) (a + d) ⊆ Ioo lo hi ∧
        ∀ b ∈ Ico a b₀,
          CompactDataExtension (ScalarSweepPath.solves (L₁₀ := L₁₀) (L₂₀ := L₂₀)
            (D₁ := D₁) (D₂ := D₂)) (productAbove e B S b hi)
            (e.symm '' (B' ×ˢ Ioo (a - d) (a + d))))
    (hInterior : ∀ V : Set (X n × X n), IsOpen V → V ⊆ D₁ ×ˢ D₂ →
      ∀ K ⊆ V, IsCompact K → ∀ m : ℕ,
      ∃ (K' : Set (X n × X n)) (C : ℝ), IsCompact K' ∧ K' ⊆ V ∧ 0 ≤ C ∧
        ∀ path : ScalarSweepPath D₁ D₂ L₁₀ L₂₀,
          ∀ᶠ t in 𝓝 (0 : ℝ), ∀ G, path.solves t V G →
          ∀ M : ℝ, 0 ≤ M → (∀ x ∈ K', |G x| ≤ M) →
          ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j G x‖ ≤ C * M) :
    ∃ O : Set ((X n) × (X n)), IsOpen O ∧ S ∪ e.symm '' (B ×ˢ Icc amin amax) ⊆ O ∧
      O ⊆ D₁ ×ˢ D₂ ∧
      (∀ path : ScalarSweepPath D₁ D₂ L₁₀ L₂₀,
        ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F, (path.left t).ProductSolvesOn (path.right t) S F →
          ∃ G, (path.left t).ProductSolvesOn (path.right t) O G ∧ EqOn G F S) ∧
      ∀ K ⊆ O, IsCompact K → ∀ m : ℕ, ∃ (L : Set (X n × X n)) (C : ℝ),
        IsCompact L ∧ L ⊆ S ∧ 0 ≤ C ∧
        ∀ path : ScalarSweepPath D₁ D₂ L₁₀ L₂₀,
          ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F, (path.left t).ProductSolvesOn (path.right t) S F →
            ∀ M : ℝ, 0 ≤ M → (∀ x ∈ L, |F x| ≤ M) →
              ∃ G, (path.left t).ProductSolvesOn (path.right t) O G ∧ EqOn G F S ∧
                ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j G x‖ ≤ C * M := by
  let solves := ScalarSweepPath.solves (D₁ := D₁) (D₂ := D₂) (L₁₀ := L₁₀) (L₂₀ := L₂₀)
  have htop' : e.symm '' (B ×ˢ Ioo amax hi) ⊆ S :=
    (image_mono (Set.prod_mono Subset.rfl Ioo_subset_Ico_self)).trans htop
  obtain ⟨O, hO, hcover, hOa, hSweep⟩ :=
    exists_compactDataExtension_across_cylinder e hB hS hlo hab hhi htarget htop' hside solves
      (fun _ _ _ _ _ hsub hF => ⟨hsub.trans hF.1, hF.2.mono hsub⟩)
      (fun path t _ _ _ _ hU hV hF hG he hseg =>
        scalar_product_eqOn_of_interval_to_seed hU hV hF.1
          (path.smoothLeft.1 t) (path.smoothRight.1 t) hF.2 hG.2 he hseg)
      (by
        intro path t ι W hW F hF he
        obtain ⟨G, hG, hEq⟩ := exists_scalar_productSolution_iUnion W hW F
          (fun i => (hF i).2) he
        exact ⟨G, ⟨iUnion_subset fun i => (hF i).1, hG⟩, hEq⟩)
      hLocal
  have hOS := (subset_union_left : S ⊆ S ∪ e.symm '' (B ×ˢ Icc amin amax)).trans hcover
  have hOD : O ⊆ D₁ ×ˢ D₂ := hOa.trans (union_subset hSD
    ((image_mono (Set.prod_mono interior_subset Subset.rfl)).trans hChartD))
  refine ⟨O, hO, hcover, hOD, ?_, ?_⟩
  · intro path
    have h := hSweep.eventually_extend (fun _ _ _ hF => hF.2.1.continuousOn) hOS path
    filter_upwards [h] with t h F hF
    obtain ⟨G, hG, hEq⟩ := h F ⟨hSD, hF⟩
    exact ⟨G, hG.2, hEq⟩
  · intro K hKV hK m
    obtain ⟨L, C, hL, hLU, hC, h⟩ :=
      hSweep.eventually_bound_iteratedFDeriv hOS (hInterior O hO hOD) K hKV hK m
    refine ⟨L, C, hL, hLU, hC, fun path => ?_⟩
    filter_upwards [h path] with t h F hF M hM hL
    obtain ⟨G, hG, he, hbound⟩ := h F ⟨hSD, hF⟩ M hM hL
    exact ⟨G, hG.2, he, hbound⟩

end CalderonPaper
