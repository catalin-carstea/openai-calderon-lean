module

public import Proof.CalderonN.SmoothBoundaryLinear

import Mathlib.Tactic

/-! Identify the unweighted Sobolev trace with the physical L² trace.
Real multiplication uses its pointwise bound on the same sphere. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim]

theorem smoothBoundarySobolev_zero_eq (hn : 3 ≤ dim) (u : SmoothData dim) :
    smoothBoundarySobolev hn 0 (by norm_num) u =
      sphereSobolevZeroEquiv (smoothSphereLift u.1 u.2) := by
  apply lp.ext
  funext k
  rw [smoothBoundarySobolev_apply,
    ← sphereSobolevCoefficientL_reconstruct 0 k (sphereSobolevZeroEquiv (smoothSphereLift u.1 u.2)),
    sphereSobolevCoefficientL_zeroEquiv]

theorem norm_smoothBoundarySobolev_zero_eq (hn : 3 ≤ dim) (u : SmoothData dim) :
    ‖smoothBoundarySobolev hn 0 (by norm_num) u‖ = ‖smoothSphereLift u.1 u.2‖ := by
  rw [smoothBoundarySobolev_zero_eq,LinearIsometryEquiv.norm_map]

@[expose] def smoothBoundaryLiftL (hn : 3 ≤ dim) : smoothBallDataSubmodule dim →ₗ[ℝ] SphereL2 dim :=
  (sphereSobolevZeroEquiv (dim:=dim)).symm.toLinearEquiv.toLinearMap.comp
    (smoothBoundarySobolevLinear hn 0 (by norm_num))

theorem smoothBoundaryLiftL_apply (hn : 3 ≤ dim) (u : smoothBallDataSubmodule dim) :
    smoothBoundaryLiftL hn u = smoothSphereLift u.1 (smoothBallData_contDiff u) := by
  change (sphereSobolevZeroEquiv (dim:=dim)).symm (smoothBoundarySobolevLinear hn 0 (by norm_num) u) = _
  rw [smoothBoundarySobolevLinear_apply,smoothBoundarySobolev_zero_eq,LinearIsometryEquiv.symm_apply_apply]

theorem norm_smoothBoundaryLift_mul_le (m u : SmoothData dim) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ z ∈ standardSphere dim, |m.1 z| ≤ C) :
    ‖smoothSphereLift (fun z => m.1 z*u.1 z) (m.2.mul u.2)‖ ≤
      C*‖smoothSphereLift u.1 u.2‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow,← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,
    smoothSphereLift_inner,smoothSphereLift_inner,← integral_const_mul]
  refine integral_mono
    ((m.2.continuous.mul u.2.continuous).comp continuous_subtype_val
      |>.mul ((m.2.continuous.mul u.2.continuous).comp continuous_subtype_val)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((u.2.continuous.comp continuous_subtype_val).mul (u.2.continuous.comp continuous_subtype_val))
      |>.const_mul (C^2) |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ?_
  intro z
  change m.1 z*u.1 z*(m.1 z*u.1 z) ≤ C^2*(u.1 z*u.1 z)
  have hm := (sq_le_sq₀ (abs_nonneg _) hC).2 (hBound z z.2)
  rw [sq_abs] at hm
  nlinarith only [mul_le_mul_of_nonneg_right hm (sq_nonneg (u.1 z))]

end CalderonN
