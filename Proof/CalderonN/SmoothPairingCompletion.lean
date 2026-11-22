module

public import Proof.CalderonN.FiniteSmoothDegreeForm

import Mathlib.Tactic

/-! An actual adjoint permits one-sided limits in a finite harmonic
bound. The limit keeps the physical smooth response in each pairing. -/

public section

noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim]

def smoothHarmonicTruncation (u : SmoothData dim) (n : ℕ) : HarmonicFiniteCoefficients dim :=
  finiteHarmonicPacket (Finset.range n) (fun k => harmonicProjection k (smoothSphereLift u.1 u.2))

theorem harmonicBoundaryFiniteL_smoothHarmonicTruncation (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (u : SmoothData dim) (n : ℕ) :
    harmonicBoundaryFiniteL s (smoothHarmonicTruncation u n) =
      sphereSobolevPartialSum s n (smoothBoundarySobolev hn s hs u) := by
  rw [smoothHarmonicTruncation,harmonicBoundaryFiniteL_packet,sphereSobolevPartialSum]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have h := sphereSobolevCoefficientL_reconstruct s k (smoothBoundarySobolev hn s hs u)
  rw [smoothBoundarySobolev_apply] at h
  exact (smul_right_injective (harmonicSphereSubspace dim k) (besselWeight_pos s k).ne' h).symm

theorem tendsto_finite_boundary_smooth (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2) (u : SmoothData dim) :
    Tendsto (fun n => harmonicBoundaryFiniteL s (smoothHarmonicTruncation u n)) atTop
      (𝓝 (smoothBoundarySobolev hn s hs u)) := by
  simpa only [harmonicBoundaryFiniteL_smoothHarmonicTruncation hn s hs] using
    tendsto_sphereSobolevPartialSum s (smoothBoundarySobolev hn s hs u)

theorem tendsto_finite_harmonic_sphere (hn : 3 ≤ dim) (u : SmoothData dim) :
    Tendsto (fun n => finiteHarmonicSphereL hn (smoothHarmonicTruncation u n)) atTop
      (𝓝 (smoothSphereLift u.1 u.2)) := by
  have h := ((sphereSobolevZeroEquiv (dim:=dim)).symm.continuous.tendsto _).comp
    (tendsto_finite_boundary_smooth hn 0 (by norm_num) u)
  rw [smoothBoundarySobolev_zero_eq hn u,LinearIsometryEquiv.symm_apply_apply] at h
  simpa only [Function.comp_def,finiteHarmonicSphereL_eq_sobolev] using h

/-- Pass an actual finite-input bound to smooth inputs by using the
adjoint before taking the first approximation limit. -/
theorem abs_smooth_pair_le_of_finite_harmonic (hn : 3 ≤ dim)
    (T Tstar : SmoothData dim → SmoothData dim)
    (hDual : ∀ u v, ⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift v.1 v.2⟫_ℝ =
      ⟪smoothSphereLift u.1 u.2,smoothSphereLift (Tstar v).1 (Tstar v).2⟫_ℝ)
    (s t C : ℝ) (hs : s ≤ 2) (ht : t ≤ 2)
    (hBound : ∀ f g : HarmonicFiniteCoefficients dim,
      let u := T (harmonicFiniteSmooth f)
      |⟪smoothSphereLift u.1 u.2,finiteHarmonicSphereL hn g⟫_ℝ| ≤
        C*‖harmonicBoundaryFiniteL s f‖*‖harmonicBoundaryFiniteL t g‖)
    (u v : SmoothData dim) :
    |⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift v.1 v.2⟫_ℝ| ≤
      C*‖smoothBoundarySobolev hn s hs u‖*‖smoothBoundarySobolev hn t ht v‖ := by
  have finiteRight (g : HarmonicFiniteCoefficients dim) :
      |⟪smoothSphereLift (T u).1 (T u).2,finiteHarmonicSphereL hn g⟫_ℝ| ≤
        C*‖smoothBoundarySobolev hn s hs u‖*‖harmonicBoundaryFiniteL t g‖ := by
    let w := harmonicFiniteSmooth g
    let W := smoothSphereLift (Tstar w).1 (Tstar w).2
    rw [finiteHarmonicSphereL_apply,hDual u w]
    have hNorm := (tendsto_finite_boundary_smooth hn s hs u).norm.const_mul C
    have hL := ((innerSL ℝ W).continuous.abs.tendsto _).comp (tendsto_finite_harmonic_sphere hn u)
    have hL' : Tendsto (fun n => |⟪finiteHarmonicSphereL hn (smoothHarmonicTruncation u n),W⟫_ℝ|)
        atTop (𝓝 |⟪smoothSphereLift u.1 u.2,W⟫_ℝ|) := by
      simp only [Function.comp_def,innerSL_apply_apply] at hL
      simpa only [real_inner_comm] using hL
    refine le_of_tendsto_of_tendsto' hL'
      (hNorm.mul_const ‖harmonicBoundaryFiniteL t g‖) fun n => ?_
    have h := hBound (smoothHarmonicTruncation u n) g
    dsimp only at h
    rw [finiteHarmonicSphereL_apply hn g,hDual,← finiteHarmonicSphereL_apply] at h
    exact h
  let U := smoothSphereLift (T u).1 (T u).2
  have hL := ((innerSL ℝ U).continuous.abs.tendsto _).comp (tendsto_finite_harmonic_sphere hn v)
  have hR := (tendsto_finite_boundary_smooth hn t ht v).norm.const_mul
    (C*‖smoothBoundarySobolev hn s hs u‖)
  exact le_of_tendsto_of_tendsto' hL hR fun n => finiteRight (smoothHarmonicTruncation v n)

end CalderonN
