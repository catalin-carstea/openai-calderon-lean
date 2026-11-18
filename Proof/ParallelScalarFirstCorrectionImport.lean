import Proof.ParallelFirstSelfCorrectionCoordinateHalfTwoJets
import Proof.ParallelScalarFirstCompletePacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace ShrinkingSpheres.ParallelEnergy

/-- The correction author supplies the genuine producer. This wrapper
only matches its stronger derivative-order range to the frozen contract.
Authorship and immutable source/object hashes are recorded in imports/. -/
theorem correction_strong_half_two_jet_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    CorrectionStrongHalfTwoJetBound Y Ω K ρ c₀ M Cj := by
  exact uniform_correction_coordinate_strong_half_two_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ

end ShrinkingSpheres.ParallelEnergy
