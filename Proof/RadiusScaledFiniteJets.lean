import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff
namespace ShrinkingSpheres.SmoothFiniteJetBound
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma radius_rescale {F : P → E} {p : P} {N : ℕ} {B r : ℝ}
    (hF : SmoothFiniteJetBound F p N (B*r^2)) (hr : 0 < r) :
    SmoothFiniteJetBound (fun x => r⁻¹ • F x) p N (B*r) := by
  have hh := hF.const_smul r⁻¹
  have hBudget : |r⁻¹| * (B*r^2) = B*r := by
    rw [abs_of_pos (inv_pos.mpr hr)]
    field_simp
  rw [hBudget] at hh
  exact hh
end ShrinkingSpheres.SmoothFiniteJetBound
