import Proof.ParallelNormAssemblyReservedScalarLeadingIntegral
import Proof.ParallelNormAssemblyReservedModelIntegral
import Proof.ParallelFirstPotential

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres.ParallelEnergy

/-- All potential-containing sectors reduce to the single independently
owned bounded scalar-transpose-defect estimate. -/
theorem uniform_corrected_potential_estimate_of_scalar_defect {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ)
    (hDefect : UniformScalarPotentialDefectEstimate Y Ω K ρ c₀ M Cj CF CT) :
    UniformCorrectedPotentialEstimate Y Ω K ρ c₀ M Cj CF CT :=
  uniform_corrected_potential_estimate_of_three_sectors K ρ c₀ M Cj CF CT
    (uniform_scalar_potential_sector_of_leading_defect K ρ c₀ M Cj CF CT
      (uniform_actual_scalar_potential_leading_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT) hDefect)
    (uniform_first_potential_cross_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)
    (uniform_corrected_model_potential_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)

end ShrinkingSpheres.ParallelEnergy
