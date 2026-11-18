import Solution

namespace ShrinkingSpheres

/-- A smooth mean-zero test in the kernel has zero four-term energy, with the same thresholds
    throughout the family of admitted radii and metrics. -/
theorem zero_energy_of_zero_output (Y Ω : Set X) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hcpt : IsCompact (closure Y)) (hin : closure Y ⊆ Ω) :
    ∃ m : ℕ, ∀ (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ),
      1 ≤ K → 0 < ρ → 0 < c₀ → ∃ floor ε₀ : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧
        ∀ d ε, 0 ≤ ε → ε ≤ ε₀ → Admissible Y Ω K ρ c₀ M Cj floor ε d →
          ∀ φ, Test Y d.γ d.frame φ → traceNorm Y d φ = 0 → energyNorm Y d φ = 0 := by
  obtain ⟨m, hm⟩ := coercivity Y Ω hY hΩ hcpt hin
  refine ⟨m, ?_⟩
  intro K ρ c₀ M Cj hK hρ hc₀
  obtain ⟨floor, ε₀, C, hf, hε, _, bound⟩ := hm K ρ c₀ M Cj hK hρ hc₀
  refine ⟨floor, ε₀, hf, hε, ?_⟩
  intro d ε hε₁ hε₂ hd φ hφ hzero
  have h := bound d ε hε₁ hε₂ hd φ hφ
  rw [hzero, mul_zero] at h
  exact le_antisymm h (Real.sqrt_nonneg _)

end ShrinkingSpheres
