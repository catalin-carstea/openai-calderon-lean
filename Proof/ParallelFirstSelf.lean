import Proof.ParallelEnergySectors
import Proof.ParallelFirstSelfFinalAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set MeasureTheory
namespace ShrinkingSpheres.ParallelEnergy

/-- Assignment scaffold. Prove this complete physical sector from the frozen premises. -/
theorem uniform_first_self_norm_comparison {Y Ω : Set X}
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
        IntegrableOn (firstSelfComplexDensity P WF W E) Y ∧
        |∫ y in Y,firstSelfComplexDensity P WF W E y| ≤
          C*ε*energySq Y d.γ d.frame d.radius φ := by
  exact uniform_first_self_norm_comparison_closed hY hΩ hSub hm K ρ c₀ M Cj hK hρ
    CF CT CB CS CG CK hCB hCS hCG hCK

end ShrinkingSpheres.ParallelEnergy
