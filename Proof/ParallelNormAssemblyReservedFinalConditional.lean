import Proof.ParallelNormAssemblyReservedPotential
import Proof.ParallelScalarModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
namespace ShrinkingSpheres.ParallelEnergy

/-- The exact complete reserved-sector target: original sectors4--8,
with integrability, SAME arbitrary packets before tests, and constants
before profiles. This is precisely the third grouped norm-comparison
bound after specializing its C4 constant. -/
def UniformReservedIntegralEstimate (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) : Prop :=
  ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ φ,Test Y d.γ d.frame φ →
    ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      IntegrableOn (reservedComplexDensity P WF W E D) Y ∧
      |∫ y in Y,reservedComplexDensity P WF W E D y| ≤
        C*ε*energySq Y d.γ d.frame d.radius φ

/-- All actual corrected sectors are closed except the one independently
owned corrected model/complete-first bound. -/
theorem uniform_corrected_reserved_estimate_of_model_first {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ)
    (hFirst : UniformCorrectedModelSectorEstimate Y Ω K ρ c₀ M Cj CF CT 1) :
    UniformCorrectedReservedEstimate Y Ω K ρ c₀ M Cj CF CT :=
  uniform_corrected_reserved_estimate_of_model_first_potential K ρ c₀ M Cj CF CT
    (uniform_corrected_model_scalar_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)
    hFirst (uniform_corrected_potential_mixed_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)

/-- Exact checked final reserved caller. Its sole open premise is the
literal corrected model/first estimate; actual model-adjoint defect
correction is discharged by the existing complete physical theorem. -/
theorem uniform_reserved_complex_density_integral_bound_of_model_first {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ)
    (hFirst : UniformCorrectedModelSectorEstimate Y Ω K ρ c₀ M Cj CF CT 1) :
    UniformReservedIntegralEstimate Y Ω K ρ c₀ M Cj CF CT :=
  uniform_reserved_complex_density_integral_bound_of_corrected hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT
    (uniform_corrected_reserved_estimate_of_model_first hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT hFirst)

end ShrinkingSpheres.ParallelEnergy
