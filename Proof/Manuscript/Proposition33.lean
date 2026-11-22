module

public import Proof.Manuscript.ScalarElliptic

import Proof.Manuscript.ScalarProductExtensionLocal
import Mathlib.Tactic

public section

open Set Filter CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

/-- Proposition 3.3. A strict product phase allows continuation from its
positive side, with fixed compact arms and estimates under smooth
perturbation of the two operators and the phase. Constant families recover
the assertion for a single product solution. -/
theorem proposition33
    {n : ℕ} [NeZero n] {D₁ D₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (L₁₀ L₂₀ : ScalarElliptic n)
    (hL₁₀ : L₁₀.SmoothOn D₁) (hL₂₀ : L₂₀.SmoothOn D₂)
    {U : Set ((X n) × (X n))} (hU : IsOpen U) (hUD : U ⊆ D₁ ×ˢ D₂)
    (z₀ : (X n) × (X n)) (hz₀ : z₀ ∈ U)
    (ρ₀ : ((X n) × (X n)) → ℝ) (hρ : ContDiffOn ℝ ∞ ρ₀ U)
    (hρ₀ : ρ₀ z₀ = 0)
    (hstrict : ProductStrictHessianAt L₁₀.metric L₂₀.metric ρ₀ z₀) :
    ∃ (V : Set ((X n) × (X n))) (K₁ K₂ K₃ K₄ : Set (X n)) (ε : ℝ),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ 0 < ε ∧
      IsCompact K₁ ∧ IsCompact K₂ ∧ IsCompact K₃ ∧ IsCompact K₄ ∧
      let K := (K₁ ×ˢ K₂) ∪ (K₃ ×ˢ K₄)
      let admissible := fun (L₁ L₂ : ℝ → ScalarElliptic n) (ρ : ℝ → ((X n) × (X n)) → ℝ) =>
        ScalarElliptic.SmoothFamilyOn L₁ D₁ ∧ ScalarElliptic.SmoothFamilyOn L₂ D₂ ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × ((X n) × (X n)) => ρ q.1 q.2) (univ ×ˢ U) ∧
        L₁ 0 = L₁₀ ∧ L₂ 0 = L₂₀ ∧ ρ 0 = ρ₀
      let side := fun (ρ : ℝ → ((X n) × (X n)) → ℝ) (a : ℝ) => {z ∈ U | 0 < ρ a z}
      (∀ L₁ L₂ ρ, admissible L₁ L₂ ρ →
        ∀ᶠ a in 𝓝 (0 : ℝ), K ⊆ {z ∈ U | ε < ρ a z}) ∧
      (∀ L₁ L₂ ρ, admissible L₁ L₂ ρ → ∀ᶠ a in 𝓝 (0 : ℝ), ∀ F,
        (L₁ a).ProductSolvesOn (L₂ a) (side ρ a) F →
        ∃ G, (L₁ a).ProductSolvesOn (L₂ a) V G ∧ EqOn G F (V ∩ side ρ a)) ∧
      ∀ H ⊆ V, IsCompact H → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ L₁ L₂ ρ, admissible L₁ L₂ ρ →
        ∀ᶠ a in 𝓝 (0 : ℝ), ∀ F, (L₁ a).ProductSolvesOn (L₂ a) (side ρ a) F →
        ∀ M : ℝ, 0 ≤ M → (∀ z ∈ K, |F z| ≤ M) →
        ∃ G, (L₁ a).ProductSolvesOn (L₂ a) V G ∧ EqOn G F (V ∩ side ρ a) ∧
          ∀ k ≤ m, ∀ z ∈ H, ‖iteratedFDeriv ℝ k G z‖ ≤ C * M := by
  obtain ⟨V,K₁,K₂,K₃,K₄,ε,hV,hzV,hVU,hε,hK₁,hK₂,hK₃,hK₄,hArms,hQual,hQuant⟩ :=
    ScalarElliptic.exists_reference_scalar_productExtension hD₁ hD₂ hL₁₀ hL₂₀ hU hUD z₀ hz₀ hρ hρ₀ hstrict
  refine ⟨V,K₁,K₂,K₃,K₄,ε,hV,hzV,hVU,hε,hK₁,hK₂,hK₃,hK₄,?_,?_,?_⟩
  · intro L₁ L₂ ρ hAdm
    exact hArms L₁ L₂ ρ ⟨hAdm.1,hAdm.2.1,hAdm.2.2.1,hAdm.2.2.2.1,hAdm.2.2.2.2.1,
      0,le_rfl,hε.le,by simpa using hAdm.2.2.2.2.2⟩
  · intro L₁ L₂ ρ hAdm
    exact hQual L₁ L₂ ρ ⟨hAdm.1,hAdm.2.1,hAdm.2.2.1,hAdm.2.2.2.1,hAdm.2.2.2.2.1,
      0,le_rfl,hε.le,by simpa using hAdm.2.2.2.2.2⟩
  · intro H hHV hH m
    obtain ⟨C,hC,hBd⟩ := hQuant H hHV hH m
    refine ⟨C,hC,?_⟩
    intro L₁ L₂ ρ hAdm
    exact hBd L₁ L₂ ρ ⟨hAdm.1,hAdm.2.1,hAdm.2.2.1,hAdm.2.2.2.1,hAdm.2.2.2.2.1,
      0,le_rfl,hε.le,by simpa using hAdm.2.2.2.2.2⟩

end CalderonPaper
