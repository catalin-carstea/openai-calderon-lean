module

public import Proof.CalderonN.PolynomialBallGreenPairing

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! The solid-harmonic bulk moment in the released Proposition 5.3
proof, using the general-dimensional polar integration already checked
for the same unit ball. -/

public section

noncomputable section
open Set MeasureTheory Metric MvPolynomial
open scoped ContDiff ENNReal InnerProductSpace
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic GreenRadialTrace

variable {dim : ℕ}

theorem polynomialEvaluation_smul_of_homogeneous {p : MvPolynomial (Fin dim) ℝ} {k : ℕ}
    (hp : p.IsHomogeneous k) (r : ℝ) (x : X dim) :
    polynomialEvaluation p (r • x) = r^k * polynomialEvaluation p x := by
  change p.eval (fun i => (r • x) i) = r^k * p.eval (fun i => x i)
  simp only [PiLp.smul_apply,smul_eq_mul]
  rw [MvPolynomial.eval_eq,MvPolynomial.eval_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,← hp.degree_eq_sum_deg_support hd]
  ring

variable [NeZero dim] [Nontrivial (Fin dim)]

/-- The bulk inner product of two homogeneous polynomials is their
sphere inner product with the exact radial volume factor. -/
theorem integral_ball_polynomialEvaluation_mul {k l : ℕ} {p q : MvPolynomial (Fin dim) ℝ}
    (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous l) :
    (∫ x in ball (0 : X dim) 1, polynomialEvaluation p x * polynomialEvaluation q x) =
      (unitSphereArea dim/((k : ℝ)+(l : ℝ)+dim)) *
        ⟪polynomialSphereL2 p,polynomialSphereL2 q⟫_ℝ := by
  let f (z : X dim) := polynomialEvaluation p z * polynomialEvaluation q z
  have hc : Continuous f := (contDiff_polynomialEvaluation p).continuous.mul
    (contDiff_polynomialEvaluation q).continuous
  have hi : IntegrableOn f (ball (0 : X dim) 1) :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall
  change (∫ z in ball (0 : X dim) 1, f z) = _
  rw [integral_ball_zero_eq_radial_interval f 1 one_pos hi]
  have hPoint (r : ℝ) (w : UnitSphere dim) : f (r • w.val) = r^(k+l)*f w.val := by
    unfold f
    rw [polynomialEvaluation_smul_of_homogeneous hp,polynomialEvaluation_smul_of_homogeneous hq,pow_add]
    ring
  have hExp : ((dim-1+k+l : ℕ) : ℝ)+1 = (k : ℝ)+(l : ℝ)+dim := by
    have hpos : 0 < dim := NeZero.pos dim
    have h : dim-1+1=dim := Nat.sub_add_cancel hpos
    push_cast
    have hh : ((dim-1 : ℕ) : ℝ)+1=dim := by exact_mod_cast h
    linarith
  have hf (r : ℝ) :
      r^(dim-1) * (∫ w : UnitSphere dim, f (r • w.val) ∂(chartSurfaceMeasure dim)) =
      r^(dim-1+k+l) * (∫ w : UnitSphere dim, f w.val ∂(chartSurfaceMeasure dim)) := by
    simp_rw [hPoint,integral_const_mul,pow_add]
    ring
  simp_rw [hf]
  rw [intervalIntegral.integral_mul_const, _root_.integral_pow, one_pow, zero_pow (by omega),sub_zero]
  have hB := integral_unitSphereArea_mul_probability (fun w : ↥(standardSphere dim) => f w)
  rw [integral_const_mul] at hB
  rw [← hB]
  have he : (∫ w : ↥(standardSphere dim), f w.val ∂(sphereProbability dim)) =
      ⟪polynomialSphereL2 p,polynomialSphereL2 q⟫_ℝ := by
    rw [← smoothSphereLift_polynomialEvaluation p,← smoothSphereLift_polynomialEvaluation q,
      smoothSphereLift_inner]
    rfl
  rw [he,hExp]
  ring

theorem integral_ball_polynomialEvaluation_sq {k : ℕ} {p : MvPolynomial (Fin dim) ℝ}
    (hp : p.IsHomogeneous k) :
    (∫ x in ball (0 : X dim) 1, polynomialEvaluation p x ^ 2) =
      (unitSphereArea dim/(2*(k : ℝ)+dim))*‖polynomialSphereL2 p‖^2 := by
  simp_rw [pow_two]
  rw [integral_ball_polynomialEvaluation_mul hp hp,real_inner_self_eq_norm_mul_norm,two_mul]

end CalderonN
