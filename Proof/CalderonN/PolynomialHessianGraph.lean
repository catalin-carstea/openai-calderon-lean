module

public import Proof.CalderonN.HarmonicBulkDerivativeMoments

import Proof.CalderonN.BallRegularity.Multiplier
import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

/-! The native Hessian bound from the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`.
The coordinate Hessian and bulk moments use the same fixed ball. -/

public section

noncomputable section
open Set MeasureTheory Metric MvPolynomial
open scoped ContDiff ENNReal Gradient InnerProductSpace
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace BallDirichlet

variable {dim : ℕ}

lemma norm_sq_linearMap_le_coordinate_squares (T : (X dim) →L[ℝ] (X dim)) :
    ‖T‖^2 ≤ ∑ j : Fin dim, ∑ i : Fin dim,
      ((T (axis i)) j)^2 := by
  let row (j : Fin dim) : (X dim) →L[ℝ] ℝ := (EuclideanSpace.proj j).comp T
  let S : ℝ := ∑ j : Fin dim, ‖row j‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => sq_nonneg ‖row j‖)
  have hPoint (v : (X dim)) : ‖T v‖^2 ≤ S*‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin dim, (row j v)^2) ≤ S*‖v‖^2
    calc
      (∑ j : Fin dim, (row j v)^2) ≤
          ∑ j : Fin dim, ‖row j‖^2*‖v‖^2 := by
        apply Finset.sum_le_sum
        intro j _
        have h := pow_le_pow_left₀ (norm_nonneg (row j v)) ((row j).le_opNorm v) 2
        simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using h
      _ = S*‖v‖^2 := by rw [Finset.sum_mul]
  have hT : ‖T‖ ≤ Real.sqrt S := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg S)
    intro v
    have h := hPoint v
    have hs : (Real.sqrt S * ‖v‖)^2 = S*‖v‖^2 := by
      rw [mul_pow, Real.sq_sqrt hS]
    have hb : 0 ≤ Real.sqrt S * ‖v‖ := mul_nonneg (Real.sqrt_nonneg S) (norm_nonneg v)
    nlinarith [norm_nonneg (T v)]
  have hsq : ‖T‖^2 ≤ S := by
    have h := pow_le_pow_left₀ (norm_nonneg T) hT 2
    simpa only [Real.sq_sqrt hS] using h
  calc
    ‖T‖^2 ≤ S := hsq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have h := (EuclideanSpace.basisFun (Fin dim) ℝ).norm_dual (row j)
      simpa only [row, axis, EuclideanSpace.basisFun_apply,
        ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj] using h

private theorem fderiv_polynomial_gradient_coord [NeZero dim] (p : MvPolynomial (Fin dim) ℝ)
    (z : X dim) (i j : Fin dim) :
    (fderiv ℝ (gradient (polynomialEvaluation p)) z (axis j)) i =
      polynomialEvaluation (pderiv j (pderiv i p)) z := by
  let g := gradient (polynomialEvaluation p)
  have hSmooth : ContDiff ℝ ∞ g :=
    (InnerProductSpace.toDual ℝ (X dim)).symm.toContinuousLinearEquiv.contDiff.comp
      ((contDiff_polynomialEvaluation p).fderiv_right (m := ∞) (by simp))
  have hg : DifferentiableAt ℝ g z := hSmooth.differentiable (by simp) z
  let U := EuclideanSpace.proj (𝕜 := ℝ) i
  have h := (U.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  have hEq : U ∘ g = polynomialEvaluation (pderiv i p) := by
    funext x
    change gradient (polynomialEvaluation p) x i = _
    rw [gradient_apply_coord]
    change coordDeriv i (polynomialEvaluation p) x = _
    rw [coordDeriv_polynomialEvaluation]
  rw [hEq] at h
  have ht := congrArg (fun L : X dim →L[ℝ] ℝ => L (axis j)) h
  change coordDeriv j (polynomialEvaluation (pderiv i p)) z = _ at ht
  rw [coordDeriv_polynomialEvaluation] at ht
  exact ht.symm

variable [NeZero dim]

private theorem integral_ball_polynomialHessian_le (p : MvPolynomial (Fin dim) ℝ) :
    (∫ z in ball (0 : X dim) 1, ‖TauCeti.iteratedGradientChain (polynomialEvaluation p) 1 z‖^2) ≤
      ∑ i : Fin dim, ∑ j : Fin dim,
        ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i p)) z ^ 2 := by
  let H := fderiv ℝ (gradient (polynomialEvaluation p))
  have hSmooth : ContDiff ℝ ∞ (gradient (polynomialEvaluation p)) :=
    (InnerProductSpace.toDual ℝ (X dim)).symm.toContinuousLinearEquiv.contDiff.comp
      ((contDiff_polynomialEvaluation p).fderiv_right (m := ∞) (by simp))
  have hH : Continuous (fun z => ‖H z‖^2) :=
    ((hSmooth.fderiv_right (m := ∞) (by simp)).continuous.norm).pow 2
  let B := ball (0 : X dim) 1
  have hi (f : X dim → ℝ) (hf : Continuous f) : IntegrableOn f B :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall
  have hC (i j : Fin dim) : IntegrableOn
      (fun z => polynomialEvaluation (pderiv j (pderiv i p)) z ^ 2) B :=
    hi _ ((contDiff_polynomialEvaluation (pderiv j (pderiv i p))).continuous.pow 2)
  have hSum : IntegrableOn (fun z : X dim => ∑ i : Fin dim, ∑ j : Fin dim,
        polynomialEvaluation (pderiv j (pderiv i p)) z ^ 2) B :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hC i j))
  change (∫ z in B, ‖H z‖^2) ≤ _
  calc
    _ ≤ ∫ z in B, ∑ i : Fin dim, ∑ j : Fin dim,
        polynomialEvaluation (pderiv j (pderiv i p)) z ^ 2 := by
      apply integral_mono_ae (hi _ hH) hSum
      filter_upwards with z
      simpa only [H,fderiv_polynomial_gradient_coord] using norm_sq_linearMap_le_coordinate_squares (H z)
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hC i j))]
      simp_rw [integral_finsetSum Finset.univ (fun j _ => hC _ j)]
      rfl

theorem norm_sq_smoothBallSobolev_polynomialEvaluation_le (p : MvPolynomial (Fin dim) ℝ) :
    let u : SmoothData dim := ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
    ‖smoothBallSobolev 2 u‖^2 ≤
      (∫ z in ball (0 : X dim) 1, polynomialEvaluation p z ^ 2) +
      (∫ z in ball (0 : X dim) 1, ‖gradient (polynomialEvaluation p) z‖^2) +
      ∑ i : Fin dim, ∑ j : Fin dim,
        ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i p)) z ^ 2 := by
  let u : SmoothData dim := ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
  let U := smoothSobolev u
  have hVal : ‖TauCeti.W1p.value U‖^2 =
      ∫ z in ball (0 : X dim) 1, polynomialEvaluation p z ^ 2 := by
    rw [← MeasureTheory.Lp.integral_norm_sq_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [value_smoothSobolev_ae u] with z hz
    rw [show (TauCeti.W1p.value U) z = polynomialEvaluation p z from hz,Real.norm_eq_abs,sq_abs]
  have hGrad : ‖TauCeti.W1p.gradient U‖^2 =
      ∫ z in ball (0 : X dim) 1, ‖gradient (polynomialEvaluation p) z‖^2 := by
    rw [← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae u] with z hz
    rw [show (TauCeti.W1p.gradient U) z = gradient (polynomialEvaluation p) z from hz]
  have hHess : ‖TauCeti.Wkp.iteratedGradient 1 (smoothBallSobolev 2 u)‖^2 =
      ∫ z in ball (0 : X dim) 1, ‖TauCeti.iteratedGradientChain (polynomialEvaluation p) 1 z‖^2 := by
    rw [← MeasureTheory.Lp.integral_norm_sq_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [iteratedGradient_smoothBallSobolev_ae 1 u] with z hz
    rw [hz]
  change ‖smoothBallSobolev 2 u‖^2 ≤ _
  rw [TauCeti.Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ 0,
    lowerOrder_smoothBallSobolev]
  change ‖U‖^2 + _ ≤ _
  rw [TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,hVal,hGrad,hHess]
  exact add_le_add le_rfl (integral_ball_polynomialHessian_le p)

end CalderonN
