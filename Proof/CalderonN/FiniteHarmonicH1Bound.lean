module

public import Proof.CalderonN.PolynomialBallSobolev
public import Proof.CalderonN.PolynomialBallMoments
public import Proof.CalderonN.GaussianSphere

import Mathlib.Tactic

/-! The first-order norm of a finite solid-harmonic lift, with the
sphere probability normalization used by the protected statement. -/

public section

noncomputable section
open MeasureTheory MvPolynomial Metric
open scoped InnerProductSpace
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic GreenRadialTrace BallDirichlet
open TauCeti

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem norm_sq_sum_of_pairwise_orthogonal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ℕ) (f : ℕ → H)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪f i, f j⟫_ℝ = 0) :
    ‖∑ k ∈ s, f k‖ ^ 2 = ∑ k ∈ s, ‖f k‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single_of_mem i hi (fun j hj hij => hf i hi j hj hij.symm),
    real_inner_self_eq_norm_sq]

/-- Bulk value and gradient contributions are separately diagonal in solid
harmonic degree. The value contribution carries the radial volume factor. -/
theorem norm_sq_finite_harmonic_polynomialBallH1 (s : Finset ℕ)
    (p : ℕ → MvPolynomial (Fin dim) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous dim k) :
    ‖polynomialBallH1L dim (∑ k ∈ s, p k)‖ ^ 2 =
      unitSphereArea dim * ∑ k ∈ s,
        (1 / (2 * (k : ℝ) + dim) + k) * ‖polynomialSphereL2 (p k)‖ ^ 2 := by
  let f (k : ℕ) : FixedBallH1 dim := polynomialBallH1L dim (p k)
  have hV (i : ℕ) (hi : i ∈ s) (j : ℕ) (hj : j ∈ s) :
      ⟪W1p.value (f i), W1p.value (f j)⟫_ℝ =
        (unitSphereArea dim / ((i : ℝ) + j + dim)) *
          ⟪polynomialSphereL2 (p i), polynomialSphereL2 (p j)⟫_ℝ := by
    rw [W1p.inner_value_eq_setIntegral, ← integral_ball_polynomialEvaluation_mul (hp i hi).1 (hp j hj).1]
    apply integral_congr_ae
    change ∀ᵐ x ∂volume.restrict (ball (0 : X dim) 1),
      W1p.value (f i) x * W1p.value (f j) x =
        polynomialEvaluation (p i) x * polynomialEvaluation (p j) x
    simp only [f, polynomialBallH1L_apply]
    filter_upwards [value_smoothSobolev_ae ⟨polynomialEvaluation (p i), contDiff_polynomialEvaluation (p i)⟩,
      value_smoothSobolev_ae ⟨polynomialEvaluation (p j), contDiff_polynomialEvaluation (p j)⟩] with x hxi hxj
    rw [hxi, hxj]
  have hG (i j : ℕ) (hj : j ∈ s) :
      ⟪W1p.gradient (f i), W1p.gradient (f j)⟫_ℝ =
        unitSphereArea dim * (j : ℝ) *
          ⟪polynomialSphereL2 (p i), polynomialSphereL2 (p j)⟫_ℝ := by
    simp only [f, polynomialBallH1L_apply, inner_nativeGradient_harmonicPolynomial
      ⟨polynomialEvaluation (p i), contDiff_polynomialEvaluation (p i)⟩ j (p j) (hp j hj),
      smoothSphereLift_polynomialEvaluation]
  have hO (i : ℕ) (hi : i ∈ s) (j : ℕ) (hj : j ∈ s) (hij : i ≠ j) :
      ⟪polynomialSphereL2 (p i), polynomialSphereL2 (p j)⟫_ℝ = 0 :=
    orthogonalSphereHarmonics dim i j hij _ (polynomialSphereL2_mem i (p i) (hp i hi))
      _ (polynomialSphereL2_mem j (p j) (hp j hj))
  have hVV : ‖∑ k ∈ s, W1p.value (f k)‖ ^ 2 = ∑ k ∈ s, ‖W1p.value (f k)‖ ^ 2 :=
    norm_sq_sum_of_pairwise_orthogonal s _ (fun i hi j hj hij => by rw [hV i hi j hj, hO i hi j hj hij, mul_zero])
  have hGG : ‖∑ k ∈ s, W1p.gradient (f k)‖ ^ 2 = ∑ k ∈ s, ‖W1p.gradient (f k)‖ ^ 2 :=
    norm_sq_sum_of_pairwise_orthogonal s _ (fun i hi j hj hij => by rw [hG i j hj, hO i hi j hj hij, mul_zero])
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq, map_sum]
  change ‖W1p.value (∑ k ∈ s, f k)‖ ^ 2 + ‖W1p.gradient (∑ k ∈ s, f k)‖ ^ 2 = _
  simp only [← W1p.valueL_apply, ← W1p.gradientL_apply, map_sum]
  simp only [W1p.valueL_apply, W1p.gradientL_apply]
  rw [hVV, hGG, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← real_inner_self_eq_norm_sq (W1p.value (f k)),
    ← real_inner_self_eq_norm_sq (W1p.gradient (f k)), hV k hk k hk, hG k k hk,
    real_inner_self_eq_norm_sq, ← two_mul]
  ring

theorem norm_sq_finite_harmonic_polynomialBallH1_le (s : Finset ℕ)
    (p : ℕ → MvPolynomial (Fin dim) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous dim k) :
    ‖polynomialBallH1L dim (∑ k ∈ s, p k)‖ ^ 2 ≤
      unitSphereArea dim * ∑ k ∈ s, (1 + (k : ℝ)) * ‖polynomialSphereL2 (p k)‖ ^ 2 := by
  rw [norm_sq_finite_harmonic_polynomialBallH1 s p hp]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (unitSphereArea_pos (dim := dim)).le
  refine mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) (sq_nonneg _)
  have hd : (1 : ℝ) ≤ dim := by exact_mod_cast NeZero.pos dim
  exact div_le_one (by positivity) |>.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])

end CalderonN
