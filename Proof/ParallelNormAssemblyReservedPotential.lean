import Proof.ParallelNormAssemblyReservedPotentialConditional
import Proof.ParallelScalarPotentialDefect

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set
namespace ShrinkingSpheres.ParallelEnergy

/-- Complete literal raw scalar/potential sector, both orientations and
real/imaginary components, in the SAME physical frozen energy. -/
theorem uniform_scalar_potential_cross_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    UniformPotentialSectorEstimate Y Ω K ρ c₀ M Cj CF CT 4 :=
  uniform_scalar_potential_sector_of_leading_defect K ρ c₀ M Cj CF CT
    (uniform_actual_scalar_potential_leading_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)
    (uniform_scalar_potential_defect_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)

/-- ALL actual potential-containing reserved sectors are now bounded,
with their genuine common-core identities and internal cancellations. -/
theorem uniform_corrected_potential_mixed_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    UniformCorrectedPotentialEstimate Y Ω K ρ c₀ M Cj CF CT :=
  uniform_corrected_potential_estimate_of_scalar_defect hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT
    (uniform_scalar_potential_defect_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)

end ShrinkingSpheres.ParallelEnergy
