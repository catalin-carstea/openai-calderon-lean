module

public import Proof.Manuscript.CompactDataExtension
public import Mathlib.Analysis.Calculus.ContDiff.Basic

public section

open Set Filter
open scoped Topology

namespace CalderonPaper

variable {X P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every continuous seed has the data bound needed for existence. -/
theorem CompactDataExtension.eventually_extend
    {solves : P → ℝ → Set X → (X → ℝ) → Prop} {U V : Set X} (h : CompactDataExtension solves U V)
    (hContinuous : ∀ path t {F}, solves path t U F → ContinuousOn F U) (hUV : U ⊆ V) :
    ∀ path : P, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F, solves path t U F →
      ∃ G, solves path t V G ∧ EqOn G F U := by
  obtain ⟨L, _, hL, hLU, _, h⟩ := h ∅ (empty_subset _) isCompact_empty
  intro path
  filter_upwards [h path] with t hf F hF
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn ((hContinuous path t hF).mono hLU)
  obtain ⟨G, hG, he, _⟩ := hf F hF (max M 0) (le_max_right _ _)
    (fun x hx => (hM x hx).trans (le_max_left _ _))
  exact ⟨G, hG, he.mono (subset_inter Subset.rfl hUV)⟩

/-- Interior derivative estimates use a compact value bound in the same
output domain, so the finite sweep supplies one compact seed data set. -/
theorem CompactDataExtension.eventually_bound_iteratedFDeriv
    {solves : P → ℝ → Set X → (X → ℝ) → Prop} {U V : Set X} (h : CompactDataExtension solves U V)
    (hUV : U ⊆ V)
    (hInterior : ∀ K ⊆ V, IsCompact K → ∀ m : ℕ,
      ∃ (K' : Set X) (B : ℝ), IsCompact K' ∧ K' ⊆ V ∧ 0 ≤ B ∧
        ∀ path : P, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ G, solves path t V G →
          ∀ A : ℝ, 0 ≤ A → (∀ x ∈ K', |G x| ≤ A) →
          ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j G x‖ ≤ B * A) :
    ∀ K ⊆ V, IsCompact K → ∀ m : ℕ, ∃ (L : Set X) (C : ℝ),
      IsCompact L ∧ L ⊆ U ∧ 0 ≤ C ∧
      ∀ path : P, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F, solves path t U F →
        ∀ M : ℝ, 0 ≤ M → (∀ x ∈ L, |F x| ≤ M) →
          ∃ G, solves path t V G ∧ EqOn G F U ∧
            ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j G x‖ ≤ C * M := by
  intro K hKV hK m
  obtain ⟨K', B, hK', hK'V, hB, hi⟩ := hInterior K hKV hK m
  obtain ⟨L, C, hL, hLU, hC, he⟩ := h K' hK'V hK'
  refine ⟨L, B * C, hL, hLU, mul_nonneg hB hC, fun path => ?_⟩
  filter_upwards [he path, hi path] with t he hi F hF M hM hFM
  obtain ⟨G, hG, hGF, hValue⟩ := he F hF M hM hFM
  refine ⟨G, hG, hGF.mono (subset_inter Subset.rfl hUV), ?_⟩
  intro j hj x hx
  simpa only [mul_assoc] using hi G hG (C * M) (mul_nonneg hC hM) hValue j hj x hx

end CalderonPaper
