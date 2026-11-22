module

public import Proof.CalderonN.ActualGaussConormalBounds
public import Proof.CalderonN.SmoothTraceSobolevCompletion

import Proof.CalderonN.SmoothTraceLinearAdjunction
import Proof.CalderonN.SmoothTraceWeightedCasimir
import Mathlib.Tactic

/-! Weak finite-harmonic matrix-element estimates and their rotations
give all order-one endpoints on the smooth angular core. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_smoothTraceOrderOne_weak_of_finite_pair (hn : 3 ≤ dim)
    (T T' : Module.End ℝ (SmoothSphereTrace dim)) (hAdj : SmoothTraceAdjoint hn T T')
    (C : ℝ) (hC : 0 ≤ C)
    (hFin : ∀ f g : HarmonicFiniteCoefficients dim,
      |⟪smoothSphereTraceL2 hn (T (finiteHarmonicSmoothTraceL f)),
        smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ| ≤
      C*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (T u)‖ ≤
      C*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ := by
  apply norm_smoothTraceOperator_le_of_finite hn (1/2:ℝ) (-(1/2):ℝ)
    (by norm_num) (by norm_num) (by norm_num) T T' hAdj C hC _ u
  intro f
  let S := smoothSphereTraceRepresentative (T (finiteHarmonicSmoothTraceL f))
  rw [← smoothSphereTrace_representative (T (finiteHarmonicSmoothTraceL f)),smoothSphereTraceSobolev_apply]
  apply norm_smoothBoundarySobolev_le_of_finite_tests hn (1/2:ℝ) (by norm_num) (by norm_num) S _
    (by positivity)
  intro g
  have h := hFin f g
  have hS : smoothSphereTrace S = T (finiteHarmonicSmoothTraceL f) := smoothSphereTrace_representative _
  rw [← hS,finiteHarmonicSmoothTraceL_apply g,smoothSphereTraceL2_apply,smoothSphereTraceL2_apply,
    smoothSphereLift_inner] at h
  exact h

theorem smoothTraceAngularBound_orderOne_of_rotated_finite_pairs (hn : 3 ≤ dim)
    (T : Module.End ℝ (SmoothSphereTrace dim)) (hAdj : SmoothTraceAdjoint hn T T)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hFin : ∀ f g : HarmonicFiniteCoefficients dim,
      |⟪smoothSphereTraceL2 hn (T (finiteHarmonicSmoothTraceL f)),
        smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ| ≤
      C*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖)
    (hRot : ∀ i j : I dim,∀ f g : HarmonicFiniteCoefficients dim,
      |⟪smoothSphereTraceL2 hn (smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f)),
        smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ| ≤
      D*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖) :
    SmoothTraceAngularBound hn 1 (max C (smoothTraceRotationLiftConstant dim C D)) T := by
  let E := max C (smoothTraceRotationLiftConstant dim C D)
  have hE : 0 ≤ E := hC.trans (le_max_left _ _)
  have hLow := norm_smoothTraceOrderOne_weak_of_finite_pair hn T T hAdj C hC hFin
  have hLowRot (i j : I dim) := norm_smoothTraceOrderOne_weak_of_finite_pair hn
    (smoothTraceAngularComm i j T) (smoothTraceAngularComm i j T)
    (SmoothTraceAdjoint.rotation_commutator_symmetric hn i j T hAdj) D hD (hRot i j)
  have hHigh := norm_smoothTrace_halfOrderHigher_of_rotation hn T C D 1 hC hD zero_le_one
    (fun u => by simpa only [mul_one] using hLow u) (fun i j u => by simpa only [mul_one,smoothTraceAngularComm] using hLowRot i j u)
  apply smoothTraceAngularBound_one_of_mid_and_high hn T T E hE hAdj
  · intro u
    simp only [traceOrderNorm_half_eq,traceOrderNorm_negHalf_eq]
    exact (hLow u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  all_goals
    intro u
    simp only [traceOrderNorm_half_eq,traceOrderNorm_threeHalf_eq]
    exact (by simpa only [mul_one] using hHigh u : _ ≤ _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem smoothTraceAngularBound_orderOne_of_scaled_rotated_finite_pairs (hn : 3 ≤ dim)
    (T : Module.End ℝ (SmoothSphereTrace dim)) (hAdj : SmoothTraceAdjoint hn T T)
    (C D scale : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hs : 0 ≤ scale)
    (hFin : ∀ f g : HarmonicFiniteCoefficients dim,
      |⟪smoothSphereTraceL2 hn (T (finiteHarmonicSmoothTraceL f)),
        smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ| ≤
      C*scale*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖)
    (hRot : ∀ i j : I dim,∀ f g : HarmonicFiniteCoefficients dim,
      |⟪smoothSphereTraceL2 hn (smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f)),
        smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ| ≤
      D*scale*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖) :
    SmoothTraceAngularBound hn 1 (max C (smoothTraceRotationLiftConstant dim C D)*scale) T := by
  have hScale : smoothTraceRotationLiftConstant dim (C*scale) (D*scale) =
      smoothTraceRotationLiftConstant dim C D*scale := by
    unfold smoothTraceRotationLiftConstant
    rw [show 2*(C*scale)^2+(dim:ℝ)^2*((D*scale)+(C*scale)*(2*(dim:ℝ)))^2 =
      (2*C^2+(dim:ℝ)^2*(D+C*(2*(dim:ℝ)))^2)*scale^2 by ring,
      Real.sqrt_mul (by positivity),Real.sqrt_sq hs]
  have h := smoothTraceAngularBound_orderOne_of_rotated_finite_pairs hn T hAdj (C*scale) (D*scale)
    (mul_nonneg hC hs) (mul_nonneg hD hs) hFin hRot
  rwa [hScale,← max_mul_of_nonneg _ _ hs] at h

end CalderonN
