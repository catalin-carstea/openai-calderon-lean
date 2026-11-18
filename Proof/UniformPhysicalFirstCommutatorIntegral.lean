import Proof.PhysicalFirstCommutatorIntegral
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual full-first mixed-adjoint commutator contribution has a
closed uniform global energy bound. One packet precedes every test, and
measurability and integrability are produced from its genuine graph. -/
theorem uniform_physical_first_commutator_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CB CS CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CB ∧ 0 ≤ CS ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ W : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      IntegrableOn (D.firstCommutatorDensity W.commLow) Y ∧
        |∫ y in Y,D.firstCommutatorDensity W.commLow y| ≤ CE*ε*energySq Y d.γ d.frame d.radius φ := by
  have hProduce := uniform_physical_first_commutator_packet hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨η,CB,CS,hη,hη1,hCB,hCS,hData⟩ := hProduce
  refine ⟨η,CB,CS,9*CS,hη,hη1,hCB,hCS,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨W⟩ := hData floor hf ε hε hSmall d hd CT P
  refine ⟨W,?_⟩
  intro φ E D hφ
  exact W.integral_density_bound hY hΩ hd hK hf hε (hSmall.trans hη1) hCS E D hφ
end ShrinkingSpheres
