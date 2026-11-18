import Proof.PhysicalTruncatedNormComparisonClosed

namespace ShrinkingSpheres

/-- Proposition 5.3, TeX label angular:coercivity. A finite background budget and common
    constants suffice for every admissible metric, radius and smooth test. -/
theorem coercivity (Y Ω : Set X) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hcpt : IsCompact (closure Y)) (hin : closure Y ⊆ Ω) :
    ∃ m : ℕ, ∀ (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ),
      1 ≤ K → 0 < ρ → 0 < c₀ → ∃ floor ε₀ C : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
        UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C := by
  -- The exact physical norm comparison combines the scalar, complete-first,
  -- potential and model cross sectors on the same genuine common packets.
  have comparison : ∃ m : ℕ,10 ≤ m ∧
      ∀ (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ),
        1 ≤ K → 0 < ρ → 0 < c₀ → ∀ CF CT : ℝ,0 ≤ CF → 0 ≤ CT →
          UniformPhysicalTruncatedNormComparison Y Ω K ρ c₀ M Cj CF CT := by
    refine ⟨10,by decide,?_⟩
    intro K ρ c₀ M Cj hK hρ hc₀ CF CT hCF hCT
    exact uniform_physical_truncated_norm_comparison_closed hY hΩ
      (fun y hy => hin (subset_closure hy)) (by decide) K ρ c₀ M Cj hK hρ CF CT hCF hCT
  obtain ⟨m,hm,produce⟩ := comparison
  refine ⟨m,?_⟩
  intro K ρ c₀ M Cj hK hρ hc₀
  exact uniformEstimate_of_physical_truncated_normComparison hY hΩ
    (fun y hy => hin (subset_closure hy)) hm K ρ c₀ M Cj hK hρ hc₀
    (produce K ρ c₀ M Cj hK hρ hc₀)

end ShrinkingSpheres
