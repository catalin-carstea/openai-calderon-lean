import Proof.PhysicalPotentialActualNorm
import Proof.UniformPhysicalPotentialQuarticForm
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

/-- Closed full physical quadratic potential norm comparison. Constants and
the actual mixed-adjoint package precede every smooth test. Higher first-word
lifts are constructed, and the bound uses the genuine H3/2 norm, not H5/2. -/
theorem uniform_physical_potential_quadratic_norm_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CG CK CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CG ∧ 0 ≤ CK ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,
      ∃ W : PhysicalPotentialQuarticData P y CG CK,∀ u : SphereSobolev (5/2:ℝ),
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticCoreL W u)=
        P.potentialQuadraticHalfL y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) ∧
      |‖P.potentialQuadraticCoreL W u‖^2-‖P.potentialQuadraticAdjointCoreL W u‖^2| ≤
        CE*ε*beta d.γ d.radius y*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u‖^2 := by
  obtain ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,hBudget,hProduce⟩ :=
    uniform_physical_potential_quartic_weak_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  refine ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CT P y hy
  obtain ⟨W,hW⟩ := hProduce floor hf ε hε hSmall d hd CT P y hy
  refine ⟨W,?_⟩
  intro u
  refine ⟨P.potentialQuadraticCoreL_balanced hy W u,?_⟩
  rw [P.potentialQuadraticCoreL_norm_difference hy W u]
  exact hW _
end ShrinkingSpheres
