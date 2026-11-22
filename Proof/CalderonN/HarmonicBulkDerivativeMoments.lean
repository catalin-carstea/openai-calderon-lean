module

public import Proof.CalderonN.PolynomialBallMoments

import Proof.CalderonN.BallRegularity.Multiplier
import Mathlib.Tactic

/-! The released Proposition 5.3 derivative moments on a solid
harmonic. The boundary and bulk normalizations are shared with the
general-dimensional Green pairing. -/

public section

noncomputable section
open Set MeasureTheory Metric MvPolynomial
open scoped ContDiff ENNReal Gradient InnerProductSpace
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem integral_ball_harmonic_gradient_sq (k : ℕ) (p : MvPolynomial (Fin dim) ℝ)
    (hp : p ∈ harmonicHomogeneous dim k) :
    (∫ z in ball (0 : X dim) 1, ‖gradient (polynomialEvaluation p) z‖^2) =
      unitSphereArea dim * (k : ℝ) * ‖polynomialSphereL2 p‖^2 := by
  let u : SmoothData dim := ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
  have h := inner_nativeGradient_harmonicPolynomial u k p hp
  change ⟪TauCeti.W1p.gradient (smoothSobolev u), TauCeti.W1p.gradient (smoothSobolev u)⟫_ℝ =
    unitSphereArea dim * (k : ℝ) * ⟪smoothSphereLift _ u.2,polynomialSphereL2 p⟫_ℝ at h
  have hS : smoothSphereLift u.1 u.2 = polynomialSphereL2 p := smoothSphereLift_polynomialEvaluation p
  rw [hS,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    ← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq] at h
  refine (integral_congr_ae ?_).trans h
  filter_upwards [gradient_smoothSobolev_ae u] with x hx
  change ‖gradient u.1 x‖^2 = ‖TauCeti.W1p.gradient (smoothSobolev u) x‖^2
  rw [hx]

omit [Nontrivial (Fin dim)] in
private theorem integrableOn_polynomialEvaluation_sq (p : MvPolynomial (Fin dim) ℝ) :
    IntegrableOn (fun z => polynomialEvaluation p z ^ 2) (ball (0 : X dim) 1) :=
  (((contDiff_polynomialEvaluation p).continuous.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall

theorem sum_integral_ball_harmonic_pderiv_sq (k : ℕ) (p : MvPolynomial (Fin dim) ℝ)
    (hp : p ∈ harmonicHomogeneous dim k) :
    (∑ i : Fin dim, ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv i p) z ^ 2) =
      unitSphereArea dim * (k : ℝ) * ‖polynomialSphereL2 p‖^2 := by
  have he (z : X dim) : ‖gradient (polynomialEvaluation p) z‖^2 =
      ∑ i : Fin dim, polynomialEvaluation (pderiv i p) z ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by
      rw [gradient_apply_coord]
      change coordDeriv i (polynomialEvaluation p) z ^ 2 = _
      rw [coordDeriv_polynomialEvaluation]
  have h := integral_ball_harmonic_gradient_sq k p hp
  simp_rw [he] at h
  rwa [integral_finsetSum Finset.univ (fun i _ => integrableOn_polynomialEvaluation_sq (pderiv i p))] at h

theorem sum_sphere_harmonic_pderiv_sq (k : ℕ) (p : MvPolynomial (Fin dim) ℝ)
    (hp : p ∈ harmonicHomogeneous dim (k+1)) :
    ∑ i : Fin dim, ‖polynomialSphereL2 (pderiv i p)‖^2 =
      (((k : ℝ)+1)*(2*(k : ℝ)+dim))*‖polynomialSphereL2 p‖^2 := by
  have hHom (i : Fin dim) : (pderiv i p).IsHomogeneous k := by
    have h := hp.1.pderiv (i := i)
    simpa only [Nat.add_sub_cancel] using h
  have h := sum_integral_ball_harmonic_pderiv_sq (k+1) p hp
  simp_rw [integral_ball_polynomialEvaluation_sq (hHom _)] at h
  rw [← Finset.mul_sum] at h
  have hDen : 0 < 2*(k : ℝ)+(dim : ℝ) := by
    have hD : (0:ℝ) < (dim : ℝ) := Nat.cast_pos.mpr (NeZero.pos dim)
    positivity
  have hR := congrArg (fun x : ℝ => (2*(k : ℝ)+dim)*x) h
  push_cast at hR
  field_simp [hDen.ne'] at hR
  apply mul_left_cancel₀ (unitSphereArea_pos (dim := dim)).ne'
  exact hR.trans (by ring)

theorem sum_integral_ball_harmonic_second_pderiv_sq (k : ℕ) (p : MvPolynomial (Fin dim) ℝ)
    (hp : p ∈ harmonicHomogeneous dim (k+1)) :
    (∑ i : Fin dim, ∑ j : Fin dim,
      ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i p)) z ^ 2) =
      unitSphereArea dim*(k : ℝ)*(((k : ℝ)+1)*(2*(k : ℝ)+dim))*‖polynomialSphereL2 p‖^2 := by
  have hMem (i : Fin dim) : pderiv i p ∈ harmonicHomogeneous dim k := by
    refine ⟨?_,?_⟩
    · simpa only [Nat.add_sub_cancel] using hp.1.pderiv (i := i)
    · rw [laplacian_pderiv,hp.2,map_zero]
  simp_rw [sum_integral_ball_harmonic_pderiv_sq k _ (hMem _)]
  rw [← Finset.mul_sum,sum_sphere_harmonic_pderiv_sq k p hp]
  ring

end CalderonN
