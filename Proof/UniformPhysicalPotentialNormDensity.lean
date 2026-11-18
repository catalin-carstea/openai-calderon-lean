import Proof.UniformPhysicalPotentialActualNorm
import Proof.PhysicalPotentialNormDensity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The complete quadratic potential has the original frozen physical
energy-density bound, including BOTH real components and all matrix crosses.
No conditional core regularity premise remains. -/
theorem uniform_physical_potential_quadratic_norm_density_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CG CK CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CG ∧ 0 ≤ CK ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,
      ∃ W : PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      |P.potentialQuadraticNormDensity E W| ≤ CE*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  obtain ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,hProduce⟩ :=
    uniform_physical_potential_quadratic_norm_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  refine ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CT P y hy
  obtain ⟨W,hW⟩ := hProduce floor hf ε hε hSmall d hd CT P y hy
  refine ⟨W,?_⟩
  intro φ E
  exact P.abs_potentialQuadraticNormDensity_le E
    (fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)) hy W hCE hε (fun u => (hW u).2)
end ShrinkingSpheres
