module

public import Proof.Manuscript.MovingTrace.RadialVelocityPairingChart
import Proof.Manuscript.PhysicalAdjointZeroDatum

public section

noncomputable section

open Set Metric CalderonN
open scoped ContDiff

namespace CalderonPaper.SmoothRadialVelocity

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {G : BallPoissonTube P dim} (A : SmoothRadialVelocity G)

/-- The normalized velocity family only uses the datum's values on the
sphere and therefore vanishes on an identically zero sphere restriction. -/
theorem operator_eq_zero_of_sphere_zero {p : P} (hp : p ∈ A.U)
    {φ : X dim → ℂ} (hφ : smoothNear φ (standardSphere dim))
    (hφ₀ : ∀ z : ↥(standardSphere dim), φ z = 0) (w : ↥(standardSphere dim)) :
    A.operator p φ w = 0 := by
  have h0 : smoothNear (0 : X dim → ℂ) (standardSphere dim) :=
    ⟨univ,isOpen_univ,subset_univ _,contDiffOn_const⟩
  have hEq : EqOn φ 0 (standardSphere dim) := fun z hz => hφ₀ ⟨z,hz⟩
  rw [A.operator_congr_on_sphere hp hφ h0 hEq w.property]
  have hO : IsOpen ((Prod.mk p) ⁻¹' G.U) :=
    G.openU.preimage (continuous_const.prodMk continuous_id)
  exact radialBallVelocityAdjoint_zero_datum _ _ hO (A.closedBall_subset_metric_room hp)
    (A.metric_smooth_at_p hp) w.property

end CalderonPaper.SmoothRadialVelocity
