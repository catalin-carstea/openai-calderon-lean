import Proof.ParallelNormAssemblyReservedFinalConditional
import Proof.ParallelModelFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres.ParallelEnergy

/-- Complete corrected reserved comparison, with all actual cross-sector
cancellations and every original uniform quantifier retained. -/
theorem uniform_corrected_reserved_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    UniformCorrectedReservedEstimate Y Ω K ρ c₀ M Cj CF CT :=
  uniform_corrected_reserved_estimate_of_model_first hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT
    (uniform_corrected_model_first_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)

/-- Complete literal physical reserved sectors4--8, integrable and bounded
by C epsilon times the ORIGINAL frozen energy. The SAME arbitrary
P/WF/W precede tests, and constants precede profiles and frames. -/
theorem uniform_reserved_complex_density_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    UniformReservedIntegralEstimate Y Ω K ρ c₀ M Cj CF CT :=
  uniform_reserved_complex_density_integral_bound_of_model_first hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT
    (uniform_corrected_model_first_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)

end ShrinkingSpheres.ParallelEnergy
