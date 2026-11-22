module

public import Proof.CalderonN.SmoothAngularCasimir
public import Proof.CalderonN.BallRegularity.NativeSmoothBallSobolev
public import Proof.CalderonN.NormalFluxDensity

import Mathlib.Tactic

/-! The harmonic-polynomial Green pairing used in the released
Proposition 5.3 sharp trace estimate, with the general-dimensional
unit ball and its existing probability-normalized sphere. -/

public section

noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Gradient InnerProductSpace
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace BallDirichlet

variable {dim : ℕ}

theorem coordDeriv_polynomialEvaluation (i : Fin dim) (p : MvPolynomial (Fin dim) ℝ) :
    coordDeriv i (polynomialEvaluation p) = polynomialEvaluation (pderiv i p) := by
  funext x
  rw [coordDeriv, fderiv_polynomialEvaluation_apply]
  simp [axis]

theorem radialDerivative_homogeneous_polynomialEvaluation (k : ℕ) (p : MvPolynomial (Fin dim) ℝ)
    (hp : p.IsHomogeneous k) (x : X dim) :
    fderiv ℝ (polynomialEvaluation p) x x = (k : ℝ) * polynomialEvaluation p x := by
  rw [fderiv_polynomialEvaluation_apply]
  have e := congrArg (fun q : MvPolynomial (Fin dim) ℝ => eval (euclideanCoordinates dim x) q)
    (polynomialEuler_homogeneous k p hp)
  simpa only [polynomialEuler, map_sum, map_mul, eval_X, eval_C, polynomialEvaluation,
    show ∀ i : Fin dim, euclideanCoordinates dim x i = x i from fun _ => rfl] using e

private theorem gradient_coordinate (u : X dim → ℝ) (x : X dim) (i : Fin dim) :
    gradient u x i = coordDeriv i u x := by
  rw [coordDeriv, ← inner_gradient_left (𝕜 := ℝ)]
  simp only [axis, EuclideanSpace.inner_single_right, conj_trivial, one_mul]

private theorem coordinate_divergence_polynomialGradient (p : MvPolynomial (Fin dim) ℝ)
    (x : X dim) :
    coordinateFluxDivergence (gradient (polynomialEvaluation p)) x =
      polynomialEvaluation (AngularPolynomial.laplacian p) x := by
  unfold coordinateFluxDivergence
  simp_rw [gradient_coordinate, coordDeriv_polynomialEvaluation]
  simp only [AngularPolynomial.laplacian, polynomialEvaluation, map_sum]

/-- The bulk energy pairing with a degree (k) solid harmonic is
(k) times the sphere pairing with the same boundary harmonic, with
the area factor for the protected probability measure. -/
theorem inner_nativeGradient_harmonicPolynomial [NeZero dim] [Nontrivial (Fin dim)]
    (u : SmoothData dim) (k : ℕ)
    (p : MvPolynomial (Fin dim) ℝ) (hp : p ∈ harmonicHomogeneous dim k) :
    ⟪TauCeti.W1p.gradient (smoothSobolev u),
      TauCeti.W1p.gradient (smoothSobolev ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩)⟫_ℝ =
      unitSphereArea dim * (k : ℝ) *
        ⟪smoothSphereLift u.1 u.2, polynomialSphereL2 p⟫_ℝ := by
  let v := polynomialEvaluation p
  have hv : ContDiff ℝ ∞ v := contDiff_polynomialEvaluation p
  have hgv : ContDiff ℝ ∞ (gradient v) :=
    (InnerProductSpace.toDual ℝ (X dim)).symm.toContinuousLinearEquiv.contDiff.comp
      (hv.fderiv_right (m := ∞) (by simp))
  let W : X dim → X dim := fun x => u.1 x • gradient v x
  have hW : ContDiff ℝ ∞ W := u.2.smul hgv
  have hDiv (x : X dim) : coordinateFluxDivergence W x = ⟪gradient u.1 x, gradient v x⟫_ℝ := by
    have hcd (i : Fin dim) : DifferentiableAt ℝ (fun z => gradient v z i) x :=
      (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hgv).differentiable (by simp)) x
    have hprod (i : Fin dim) :
        coordDeriv i (fun z => W z i) x =
          u.1 x * coordDeriv i (fun z => gradient v z i) x +
            coordDeriv i u.1 x * gradient v x i := by
      change coordDeriv i (fun z => u.1 z * gradient v z i) x = _
      simp only [coordDeriv, fderiv_fun_mul (u.2.differentiable (by simp) x) (hcd i),
        add_apply, smul_apply, smul_eq_mul]
      ring
    have hz : coordinateFluxDivergence (gradient v) x = 0 := by
      rw [coordinate_divergence_polynomialGradient p x, hp.2]
      exact map_zero (eval (euclideanCoordinates dim x))
    change (∑ i, coordDeriv i (fun z => W z i) x) = _
    simp_rw [hprod]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← coordinateFluxDivergence, hz, mul_zero, zero_add]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      gradient_coordinate, mul_comm]
  have hBulk :
      ⟪TauCeti.W1p.gradient (smoothSobolev u),
        TauCeti.W1p.gradient (smoothSobolev ⟨v,hv⟩)⟫_ℝ =
      ∫ x in ball (0 : X dim) 1, coordinateFluxDivergence W x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae u, gradient_smoothSobolev_ae ⟨v,hv⟩] with x hu hv'
    rw [hu,hv',hDiv]
  have hSphere : smoothSphereLift v hv = polynomialSphereL2 p :=
    smoothSphereLift_polynomialEvaluation p
  rw [hBulk, integral_unitBall_coordinateFluxDivergence W hW, ← hSphere,
    smoothSphereLift_inner, unitSphereFlux, ← integral_unitSphereArea_mul_probability,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  rw [show ⟪(w : X dim), W w⟫_ℝ = u.1 w * fderiv ℝ v w w by
    change ⟪(w : X dim), u.1 w • gradient v w⟫_ℝ = _
    rw [real_inner_smul_right,real_inner_comm,inner_gradient_left]]
  rw [radialDerivative_homogeneous_polynomialEvaluation k p hp.1]
  change unitSphereArea dim * (u.1 w * ((k : ℝ) * v w)) = _
  ring

end CalderonN
