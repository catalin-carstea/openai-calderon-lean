import Proof.PhysicalPotentialNormIntegral
import Proof.UniformPhysicalPotentialNormDensity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Closed common uniform global energy bound for the complete actual
quadratic-potential norm difference. ONE physical mixed-adjoint family is
chosen before every test, and integrability is proved from genuine harmonic
coordinates and physical adjunction. -/
theorem uniform_physical_potential_quadratic_norm_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CG CK CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CG ∧ 0 ≤ CK ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,Test Y d.γ d.frame φ →
        IntegrableOn (P.potentialQuadraticNormDensityFamily E W) Y ∧
        |∫ y in Y,P.potentialQuadraticNormDensityFamily E W y| ≤ CE*ε*energySq Y d.γ d.frame d.radius φ := by
  classical
  obtain ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,hProduce⟩ :=
    uniform_physical_potential_quadratic_norm_density_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  refine ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  let W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK :=
    fun y hy => Classical.choose (hProduce floor hf ε hε hSmall d hd CT P y hy)
  refine ⟨W,?_⟩
  intro φ E hφ
  apply P.integral_potentialQuadraticNormDensity_bound hY hSub hd hK hf hCE hε W E hφ
  intro y hy
  exact Classical.choose_spec (hProduce floor hf ε hε hSmall d hd CT P y hy) φ E
end ShrinkingSpheres
