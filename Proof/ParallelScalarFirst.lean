import Proof.ParallelScalarFirstClosedJet

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace ShrinkingSpheres.ParallelEnergy

/-- The exact paired scalar-second / complete-first cross estimate,
with the original physical operators, fixed packets, real/imaginary
components, factor two and uniform profile/frame quantifiers. -/
theorem uniform_scalar_first_cross_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT CB CS CG CK : ℝ)
    (hCF : 0 ≤ CF) (hCT : 0 ≤ CT) (hCB : 0 ≤ CB) (hCS : 0 ≤ CS)
    (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        IntegrableOn (scalarFirstComplexDensity P WF W E) Y ∧
        |∫ y in Y,scalarFirstComplexDensity P WF W E y| ≤
          C*ε*energySq Y d.γ d.frame d.radius φ := by
  have hJet : ScalarFirstJetBound Y Ω K ρ c₀ M Cj CF CT CB CS :=
    uniform_scalar_first_jet_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT CB CS
  exact uniform_scalar_first_cross_bound_of_jet_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ
    CF CT CB CS CG CK hCG hCK hJet

end ShrinkingSpheres.ParallelEnergy
