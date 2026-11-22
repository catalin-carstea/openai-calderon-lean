module

public import Proof.CalderonN.SmoothTraceHigherLift
public import Proof.CalderonN.SmoothTraceSobolevCompletion

import Proof.CalderonN.ActualFiniteRadialMidpoint
import Mathlib.Tactic

/-! Exact norms and adjoints on the smooth trace core transfer angular
bounds across the Sobolev duality. -/

public section

noncomputable section
open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2900000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_smoothTraceSobolev_le_of_finite_tests (hn : 3 ≤ dim) (s : ℝ)
    (hs : s ≤ 2) (hns : -s ≤ 2) (u : SmoothSphereTrace dim)
    (C : ℝ) (hC : 0 ≤ C)
    (hPair : ∀ f,
      |⟪smoothSphereTraceL2 hn u,smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL f)⟫_ℝ| ≤
        C*‖harmonicBoundaryFiniteL (-s) f‖) :
    ‖smoothSphereTraceSobolev hn s hs u‖ ≤ C := by
  let U := smoothSphereTraceRepresentative u
  have hU : smoothSphereTrace U = u := smoothSphereTrace_representative u
  rw [← hU,smoothSphereTraceSobolev_apply]
  have h := norm_smoothBoundarySobolev_le_of_finite_tests hn (-s) hns (by linarith) U C hC (fun f => by
    have h := hPair f
    rw [← hU,smoothSphereTraceL2_apply,finiteHarmonicSmoothTraceL_apply,smoothSphereTraceL2_apply,
      smoothSphereLift_inner] at h
    exact h)
  rw [smoothBoundarySobolev_order_eq hn (neg_neg s) _ hs] at h
  exact h

theorem norm_smoothTrace_adjoint_of_bound (hn : 3 ≤ dim) (s t : ℝ)
    (hs : s ≤ 2) (ht : t ≤ 2) (hns : -s ≤ 2) (hnt : -t ≤ 2)
    (T Tadj : Module.End ℝ (SmoothSphereTrace dim)) (hAdj : SmoothTraceAdjoint hn T Tadj)
    (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ u, ‖smoothSphereTraceSobolev hn t ht (T u)‖ ≤
      C*‖smoothSphereTraceSobolev hn s hs u‖) (v : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (-s) hns (Tadj v)‖ ≤
      C*‖smoothSphereTraceSobolev hn (-t) hnt v‖ := by
  apply norm_smoothTraceSobolev_le_of_finite_tests hn (-s) hns (by linarith) (Tadj v) _
    (mul_nonneg hC (norm_nonneg _))
  intro f
  let u := finiteHarmonicSmoothTraceL f
  change |⟪smoothSphereTraceL2 hn (Tadj v),smoothSphereTraceL2 hn u⟫_ℝ| ≤ _
  rw [real_inner_comm,← hAdj u v]
  have hCauchy := abs_smoothTrace_inner_le_sobolev hn (-t) hnt (by linarith) (T u) v
  rw [smoothSphereTraceSobolev_order_eq hn (neg_neg t) _ ht] at hCauchy
  refine hCauchy.trans ((mul_le_mul_of_nonneg_right (hT u) (norm_nonneg _)).trans_eq ?_)
  change (C*‖smoothSphereTraceSobolev hn s hs (finiteHarmonicSmoothTraceL f)‖)*
    ‖smoothSphereTraceSobolev hn (-t) hnt v‖ =
      C*‖smoothSphereTraceSobolev hn (-t) hnt v‖*‖harmonicBoundaryFiniteL (- -s) f‖
  rw [neg_neg,finiteHarmonicSmoothTraceL_sobolev]
  ring

@[expose] def smoothTraceRotationLiftConstant (dim : ℕ) (C D : ℝ) : ℝ :=
  Real.sqrt (2*C^2+(dim:ℝ)^2*(D+C*(2*(dim:ℝ)))^2)

/-- The one-rotation graph bound preserves a common positive parameter
in both initial operator bounds. -/
theorem norm_smoothTrace_halfOrderHigher_of_rotation (hn : 3 ≤ dim)
    (T : Module.End ℝ (SmoothSphereTrace dim)) (C D scale : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hScale : 0 ≤ scale)
    (hT : ∀ u, ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (T u)‖ ≤
      C*scale*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖)
    (hK : ∀ (i j : Fin dim) u,
      ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num)
        ((smoothSphereTraceRotation i j*T-T*smoothSphereTraceRotation i j) u)‖ ≤
      D*scale*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (T u)‖ ≤
      smoothTraceRotationLiftConstant dim C D*scale*
        ‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖ := by
  have h := norm_smoothSphereTrace_higher_of_rotation hn (-(1/2):ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
    T (C*scale) (D*scale) (by positivity) (by positivity) hT hK u
  rw [smoothSphereTraceSobolev_order_eq hn (show (-(1/2):ℝ)+1 = 1/2 by norm_num) _ (by norm_num),
    smoothSphereTraceSobolev_order_eq hn (show (1/2:ℝ)+1 = 3/2 by norm_num) _ (by norm_num)] at h
  refine h.trans_eq ?_
  have hFactor : 2*(C*scale)^2+(dim:ℝ)^2*(D*scale+C*scale*(2*(dim:ℝ)))^2 =
      scale^2*(2*C^2+(dim:ℝ)^2*(D+C*(2*(dim:ℝ)))^2) := by ring
  rw [hFactor,Real.sqrt_mul (sq_nonneg scale),Real.sqrt_sq hScale]
  dsimp only [smoothTraceRotationLiftConstant]
  ring

end CalderonN
