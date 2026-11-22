module

public import Proof.CalderonN.FiniteHarmonicH1Bound
public import Proof.CalderonN.SphereSobolevCompletion
public import Proof.CalderonN.SmoothSphereRotationProjection

import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

/-! Dimension-general version of the released finite harmonic lift and
its first-order completion. -/

public section

set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory Set
open scoped DirectSum Topology ENNReal Classical
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic BallDirichlet

variable {dim : ℕ} [NeZero dim]

abbrev HarmonicFiniteCoefficients (dim : ℕ) [NeZero dim] :=
  DirectSum ℕ (fun k => ↥(harmonicSphereSubspace dim k))

def harmonicPolynomialEquiv (k : ℕ) :
    harmonicHomogeneous dim k ≃ₗ[ℝ] harmonicSphereSubspace dim k :=
  LinearEquiv.ofBijective (harmonicPolynomialSphereMap k) ⟨by
    intro p q h
    apply Subtype.ext
    exact (polynomialSphereL2_injective_degree (sphereFischerInner dim) k p q
      p.property q.property).mp (congrArg Subtype.val h), harmonicPolynomialSphereMap_surjective k⟩

def harmonicPolynomialRepresentativeL (k : ℕ) :
    harmonicSphereSubspace dim k →ₗ[ℝ] MvPolynomial (Fin dim) ℝ :=
  (harmonicHomogeneous dim k).subtype.comp (harmonicPolynomialEquiv k).symm.toLinearMap

theorem harmonicPolynomialRepresentative_mem (k : ℕ)
    (a : harmonicSphereSubspace dim k) :
    harmonicPolynomialRepresentativeL k a ∈ harmonicHomogeneous dim k :=
  ((harmonicPolynomialEquiv k).symm a).property

theorem polynomialSphereL2_harmonicPolynomialRepresentative (k : ℕ)
    (a : harmonicSphereSubspace dim k) :
    polynomialSphereL2 (harmonicPolynomialRepresentativeL k a) = a.val := by
  have h := congrArg Subtype.val ((harmonicPolynomialEquiv k).apply_symm_apply a)
  exact h

@[expose] def harmonicBoundaryFiniteL (s : ℝ) : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim s :=
  DirectSum.toModule ℝ ℕ _ (fun k => (sphereSobolevSingleL s k).toLinearMap)

theorem harmonicBoundaryFiniteL_eq_sum (s : ℝ) (a : HarmonicFiniteCoefficients dim) :
    harmonicBoundaryFiniteL s a =
      ∑ k ∈ a.support, sphereSobolevSingleL s k (a k) := by
  conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact DirectSum.toModule_lof (R := ℝ)
    (φ := fun j => (sphereSobolevSingleL s j).toLinearMap) k (a k)

theorem denseRange_harmonicBoundaryFiniteL (s : ℝ) :
    DenseRange (harmonicBoundaryFiniteL (dim := dim) s) := by
  intro u
  have hmem (n : ℕ) : sphereSobolevPartialSum s n u ∈ Set.range (harmonicBoundaryFiniteL s) := by
    refine ⟨∑ k ∈ Finset.range n, DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace dim k)) k
      (sphereSobolevCoefficientL s k u), ?_⟩
    simp only [map_sum, harmonicBoundaryFiniteL, DirectSum.toModule_lof, sphereSobolevPartialSum,
      ContinuousLinearMap.coe_coe]
  exact isClosed_closure.mem_of_tendsto (tendsto_sphereSobolevPartialSum s u)
    (Filter.Eventually.of_forall fun n => subset_closure (hmem n))

theorem norm_sq_finite_boundary_sum (s : ℝ) (t : Finset ℕ)
    (a : ∀ k : ℕ, harmonicSphereSubspace dim k) :
    ‖∑ k ∈ t, sphereSobolevSingleL s k (a k)‖ ^ 2 =
      ∑ k ∈ t, besselWeight s k ^ 2 * ‖a k‖ ^ 2 := by
  have hSingle (k : ℕ) : sphereSobolevSingleL s k (a k) =
      lp.single (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 k
        (besselWeight s k • a k) := by
    rw [sphereSobolevSingleL]
    change besselWeight s k • lp.single (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 k (a k) = _
    rw [lp.single_smul]
  simp_rw [hSingle]
  have h := lp.norm_sum_single (E := fun j : ℕ => harmonicSphereSubspace dim j)
    (p := 2) (show 0 < (2 : ℝ≥0∞).toReal by norm_num) (fun k => besselWeight s k • a k) t
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_smul, Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos s _), mul_pow] using h

theorem besselWeight_one_half_sq (k : ℕ) :
    besselWeight (1/2 : ℝ) k ^ 2 = 1+(k : ℝ) := by
  unfold besselWeight
  rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : 0 ≤ 1+(k : ℝ))]
  norm_num

def harmonicFirstOrderFiniteL : HarmonicFiniteCoefficients dim →ₗ[ℝ] FixedBallH1 dim :=
  DirectSum.toModule ℝ ℕ _ (fun k => (polynomialBallH1L dim).comp (harmonicPolynomialRepresentativeL k))

theorem harmonicFirstOrderFiniteL_eq_polynomial (a : HarmonicFiniteCoefficients dim) :
    harmonicFirstOrderFiniteL a = polynomialBallH1L dim
      (∑ k ∈ a.support, harmonicPolynomialRepresentativeL k (a k)) := by
  conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact DirectSum.toModule_lof (R := ℝ)
    (φ := fun j => (polynomialBallH1L dim).comp (harmonicPolynomialRepresentativeL j)) k (a k)

variable [Nontrivial (Fin dim)]

theorem norm_harmonicFirstOrderFiniteL_le (a : HarmonicFiniteCoefficients dim) :
    ‖harmonicFirstOrderFiniteL a‖ ≤ Real.sqrt (unitSphereArea dim) * ‖harmonicBoundaryFiniteL (1/2 : ℝ) a‖ := by
  have h := norm_sq_finite_harmonic_polynomialBallH1_le a.support
    (fun k => harmonicPolynomialRepresentativeL k (a k))
    (fun k _ => harmonicPolynomialRepresentative_mem k (a k))
  simp only [polynomialSphereL2_harmonicPolynomialRepresentative] at h
  change ‖polynomialBallH1L dim (∑ k ∈ a.support, harmonicPolynomialRepresentativeL k (a k))‖ ^ 2 ≤
    unitSphereArea dim * ∑ k ∈ a.support, (1+(k : ℝ))*‖a k‖^2 at h
  simp only [harmonicFirstOrderFiniteL_eq_polynomial, harmonicBoundaryFiniteL_eq_sum]
  have hs : (Real.sqrt (unitSphereArea dim) *
      ‖∑ k ∈ a.support, sphereSobolevSingleL (1/2 : ℝ) k (a k)‖) ^ 2 =
      unitSphereArea dim * ∑ k ∈ a.support, (1+(k : ℝ))*‖a k‖^2 := by
    rw [mul_pow, Real.sq_sqrt (unitSphereArea_pos (dim := dim)).le,
      norm_sq_finite_boundary_sum]
    simp only [besselWeight_one_half_sq]
  rw [← hs] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp h

def harmonicFirstOrderLift (dim : ℕ) [NeZero dim] :
    SphereSobolev dim (1/2 : ℝ) →L[ℝ] FixedBallH1 dim :=
  LinearMap.extendOfNorm (E := HarmonicFiniteCoefficients dim)
    harmonicFirstOrderFiniteL (harmonicBoundaryFiniteL (1/2 : ℝ))

theorem harmonicFirstOrderLift_finite (a : HarmonicFiniteCoefficients dim) :
    harmonicFirstOrderLift dim (harmonicBoundaryFiniteL (1/2 : ℝ) a) = harmonicFirstOrderFiniteL a := by
  unfold harmonicFirstOrderLift
  exact LinearMap.extendOfNorm_eq (denseRange_harmonicBoundaryFiniteL (1/2 : ℝ))
    ⟨Real.sqrt (unitSphereArea dim), norm_harmonicFirstOrderFiniteL_le⟩ a

theorem norm_harmonicFirstOrderLift_le (u : SphereSobolev dim (1/2 : ℝ)) :
    ‖harmonicFirstOrderLift dim u‖ ≤ Real.sqrt (unitSphereArea dim) * ‖u‖ := by
  unfold harmonicFirstOrderLift
  exact LinearMap.norm_extendOfNorm_apply_le (denseRange_harmonicBoundaryFiniteL (1/2 : ℝ))
    (Real.sqrt (unitSphereArea dim)) norm_harmonicFirstOrderFiniteL_le u

end CalderonN
