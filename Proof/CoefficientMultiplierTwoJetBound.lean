import Proof.NativeBulkMultiplierForcingBound
import Proof.Archive.CollaboratorFixedSobolevCalculusOct17

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- The native multiplier norm controls exactly the two spatial gradient
budgets used by the gained commutator estimates. -/
theorem coefficient_multiplier_two_jet_bound (Q : SmoothCoefficientJets 3) :
    (∀ j : I,∀ z : X,|(gradient (coefficientValue 3 Q) z) j| ≤ ‖Q‖) ∧
    (∀ j : I,∀ z : X,‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ ‖Q‖) := by
  have hb (j : ℕ) (hj : j ≤ 2) (z : X) : ‖iteratedFDeriv ℝ j (coefficientValue 3 Q) z‖ ≤ ‖Q‖ :=
    norm_iteratedFDeriv_coefficientValue_le 3 Q j (by omega) z
  have hPartial (i : I) := partial_bounds (k:=0) (contDiff_coefficientValue 3 Q) i hb
  constructor
  · intro i z
    rw [gradient_apply_coord]
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hPartial i 0 (by omega) z
  · intro i z
    simp_rw [gradient_apply_coord]
    rw [TauCeti.norm_gradient_eq_norm_fderiv]
    simpa only [norm_iteratedFDeriv_one] using hPartial i 1 (by omega) z

end ShrinkingSpheres
