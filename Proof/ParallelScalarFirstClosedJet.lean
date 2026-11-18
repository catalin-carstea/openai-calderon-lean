import Proof.ParallelScalarFirstJetIntegral
import Proof.ParallelScalarFirstUniformForwardPacket
import Proof.ParallelScalarFirstCorrectionImport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres.ParallelEnergy

/-- Closed actual coefficient-jet sector, with the complete SAME physical
first coefficient and every admitted profile/frame. -/
theorem uniform_scalar_first_jet_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CF CT CB CS : ℝ) : ScalarFirstJetBound Y Ω K ρ c₀ M Cj CF CT CB CS := by
  exact uniform_scalar_first_jet_bound_of_forward_packets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
    (uniform_effective_first_forward_strong_half_two_jets_of_correction hY hΩ hSub hm K ρ c₀ M Cj hK hρ
      (correction_strong_half_two_jet_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ)) CF CT CB CS

end ShrinkingSpheres.ParallelEnergy
