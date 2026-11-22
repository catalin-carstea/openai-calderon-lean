module

public import Proof.CalderonN.PolynomialHessianGraph
public import Proof.CalderonN.PolynomialBallSobolev

import Proof.CalderonN.BallRegularity.Multiplier
import Proof.CalderonN.FiniteHarmonicH1Bound
import Proof.CalderonN.HarmonicDecomposition
import Mathlib.Tactic

/-! The high-degree finite harmonic lift estimate from the Proposition
5.3 release, in the native Sobolev graph norm in arbitrary dimension. -/

public section

noncomputable section
open Set MeasureTheory Metric MvPolynomial
open scoped ContDiff Gradient InnerProductSpace
set_option maxHeartbeats 3100000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem integral_polynomialEvaluation_sum_sq
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin dim) ℝ)
    (hOrth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ z in ball (0 : X dim) 1, polynomialEvaluation (p i) z * polynomialEvaluation (p j) z) = 0) :
    (∫ z in ball (0 : X dim) 1, polynomialEvaluation (∑ i ∈ s, p i) z ^ 2) =
      ∑ i ∈ s, ∫ z in ball (0 : X dim) 1, polynomialEvaluation (p i) z ^ 2 := by
  classical
  have hInt (i j : ℕ) : IntegrableOn
      (fun z => polynomialEvaluation (p i) z * polynomialEvaluation (p j) z) (ball (0 : X dim) 1) :=
    (((contDiff_polynomialEvaluation (p i)).continuous.mul
      (contDiff_polynomialEvaluation (p j)).continuous).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall
  have hFun (z : X dim) : polynomialEvaluation (∑ i ∈ s, p i) z ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, polynomialEvaluation (p i) z * polynomialEvaluation (p j) z := by
    simp only [polynomialEvaluation,map_sum,pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp_rw [hFun]
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => hInt i j))]
  simp_rw [integral_finsetSum s (fun j _ => hInt _ j)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => hOrth i hi j hj hji.symm)]
  simp only [pow_two]

private theorem integral_harmonicEvaluation_sum_sq
    (s : Finset ℕ) (k : ℕ → ℕ) (p : ℕ → MvPolynomial (Fin dim) ℝ)
    (hInject : Function.Injective k)
    (hp : ∀ i ∈ s, p i ∈ harmonicHomogeneous dim (k i)) :
    (∫ z in ball (0 : X dim) 1, polynomialEvaluation (∑ i ∈ s, p i) z ^ 2) =
      ∑ i ∈ s, ∫ z in ball (0 : X dim) 1, polynomialEvaluation (p i) z ^ 2 := by
  apply integral_polynomialEvaluation_sum_sq
  intro i hi j hj hij
  rw [integral_ball_polynomialEvaluation_mul (hp i hi).1 (hp j hj).1]
  have h := orthogonalSphereHarmonics dim (k i) (k j) (fun e => hij (hInject e))
    (polynomialSphereL2 (p i)) (polynomialSphereL2_mem _ _ (hp i hi))
    (polynomialSphereL2 (p j)) (polynomialSphereL2_mem _ _ (hp j hj))
  rw [h,mul_zero]

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem harmonicHomogeneous_pderiv {k : ℕ} {p : MvPolynomial (Fin dim) ℝ}
    (hp : p ∈ harmonicHomogeneous dim (k+1)) (i : Fin dim) :
    pderiv i p ∈ harmonicHomogeneous dim k := by
  refine ⟨?_,?_⟩
  · simpa only [Nat.add_sub_cancel] using hp.1.pderiv (i := i)
  · rw [laplacian_pderiv,hp.2,map_zero]

omit [Nontrivial (Fin dim)] in
private theorem integral_ball_polynomialEvaluation_gradient_coords (p : MvPolynomial (Fin dim) ℝ) :
    (∫ z in ball (0 : X dim) 1, ‖gradient (polynomialEvaluation p) z‖^2) =
      ∑ i : Fin dim, ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv i p) z ^ 2 := by
  have h (z : X dim) : ‖gradient (polynomialEvaluation p) z‖^2 =
      ∑ i : Fin dim, polynomialEvaluation (pderiv i p) z ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [gradient_apply_coord]
    change coordDeriv i (polynomialEvaluation p) z ^ 2 = _
    rw [coordDeriv_polynomialEvaluation]
  simp_rw [h]
  rw [integral_finsetSum Finset.univ]
  intro i _
  exact (((contDiff_polynomialEvaluation (pderiv i p)).continuous.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall

/-- A finite sum of positive high modes has bulk (H^2) norm controlled
by the boundary (H^{3/2}) energy with the canonical spherical measure.
Index (k) denotes degree (k+2). -/
theorem norm_sq_finite_harmonic_H2_lift_le (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin dim) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous dim (k+2)) :
    let q := ∑ k ∈ s, p k
    let u : SmoothData dim := ⟨polynomialEvaluation q,contDiff_polynomialEvaluation q⟩
    ‖smoothBallSobolev 2 u‖^2 ≤ ((dim : ℝ)+4)*unitSphereArea dim *
      ∑ k ∈ s, ((k : ℝ)+3)^3 * ‖polynomialSphereL2 (p k)‖^2 := by
  classical
  let q := ∑ k ∈ s, p k
  let u : SmoothData dim := ⟨polynomialEvaluation q,contDiff_polynomialEvaluation q⟩
  let A := unitSphereArea dim
  have hA : 0 ≤ A := (unitSphereArea_pos (dim := dim)).le
  have hp1 (i : Fin dim) (k : ℕ) (hk : k ∈ s) : pderiv i (p k) ∈ harmonicHomogeneous dim (k+1) :=
    harmonicHomogeneous_pderiv (k := k+1) (hp k hk) i
  have hp2 (i j : Fin dim) (k : ℕ) (hk : k ∈ s) :
      pderiv j (pderiv i (p k)) ∈ harmonicHomogeneous dim k :=
    harmonicHomogeneous_pderiv (hp1 i k hk) j
  have hv : (∫ z in ball (0 : X dim) 1, polynomialEvaluation q z ^ 2) =
      ∑ k ∈ s, (A/(2*((k : ℝ)+2)+dim))*‖polynomialSphereL2 (p k)‖^2 := by
    change (∫ z in ball (0 : X dim) 1, polynomialEvaluation (∑ k ∈ s, p k) z ^ 2) = _
    rw [integral_harmonicEvaluation_sum_sq s (fun k => k+2) p (fun _ _ e => Nat.add_right_cancel e) hp]
    apply Finset.sum_congr rfl
    intro k hk
    simpa only [Nat.cast_add,Nat.cast_ofNat] using integral_ball_polynomialEvaluation_sq (hp k hk).1
  have hg : (∫ z in ball (0 : X dim) 1, ‖gradient (polynomialEvaluation q) z‖^2) =
      ∑ k ∈ s, A*((k : ℝ)+2)*‖polynomialSphereL2 (p k)‖^2 := by
    rw [integral_ball_polynomialEvaluation_gradient_coords]
    have he (i : Fin dim) : (∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv i q) z ^ 2) =
        ∑ k ∈ s, ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv i (p k)) z ^ 2 := by
      change (∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv i (∑ k ∈ s, p k)) z ^ 2) = _
      rw [map_sum]
      exact integral_harmonicEvaluation_sum_sq s (fun k => k+1) (fun k => pderiv i (p k))
        (fun _ _ e => Nat.add_right_cancel e) (hp1 i)
    simp_rw [he]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    simpa only [Nat.cast_add,Nat.cast_ofNat] using sum_integral_ball_harmonic_pderiv_sq (k+2) (p k) (hp k hk)
  have hh : (∑ i : Fin dim, ∑ j : Fin dim,
        ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i q)) z ^ 2) =
      ∑ k ∈ s, A*((k : ℝ)+1)*(((k : ℝ)+2)*(2*((k : ℝ)+1)+dim))*‖polynomialSphereL2 (p k)‖^2 := by
    have he (i j : Fin dim) : (∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i q)) z ^ 2) =
        ∑ k ∈ s, ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i (p k))) z ^ 2 := by
      change (∫ z in ball (0 : X dim) 1, polynomialEvaluation
        (pderiv j (pderiv i (∑ k ∈ s, p k))) z ^ 2) = _
      rw [map_sum,map_sum]
      exact integral_harmonicEvaluation_sum_sq s id (fun k => pderiv j (pderiv i (p k)))
        Function.injective_id (hp2 i j)
    simp_rw [he]
    rw [Finset.sum_comm (f := fun (i j : Fin dim) => ∑ k ∈ s,
      ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i (p k))) z ^ 2)]
    conv_lhs =>
      enter [2,j]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
    have h := sum_integral_ball_harmonic_second_pderiv_sq (k+1) (p k) (hp k hk)
    push_cast at h
    convert h using 1 <;> ring
  change ‖smoothBallSobolev 2 u‖^2 ≤ _
  refine (norm_sq_smoothBallSobolev_polynomialEvaluation_le q).trans ?_
  rw [hv,hg,hh,← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  let x : ℝ := k
  let d : ℝ := dim
  have hx : 0 ≤ x := Nat.cast_nonneg k
  have hd : 0 ≤ d := Nat.cast_nonneg dim
  have hDen : 0 < 2*(x+2)+d := by positivity
  have h1 : 1/(2*(x+2)+d) ≤ (x+3)^3 := by
    refine ((div_le_one hDen).mpr (by linarith)).trans ?_
    exact one_le_pow₀ (by linarith)
  have h2 : x+2 ≤ (x+3)^3 := by
    have h := one_le_pow₀ (show 1 ≤ x+3 by linarith) (n := 2)
    nlinarith only [mul_le_mul_of_nonneg_right h (show 0 ≤ x+3 by positivity)]
  have h3 : (x+1)*((x+2)*(2*(x+1)+d)) ≤ (d+2)*(x+3)^3 := by
    calc
      _ ≤ (x+3)*((x+3)*((d+2)*(x+3))) := by
        apply mul_le_mul (by linarith)
        · apply mul_le_mul (by linarith)
          · nlinarith only [mul_nonneg hd hx,hd]
          · positivity
          · positivity
        · positivity
        · positivity
      _ = _ := by ring
  have hW : 1/(2*(x+2)+d)+(x+2)+(x+1)*((x+2)*(2*(x+1)+d)) ≤ (d+4)*(x+3)^3 :=
    (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hA)
    (sq_nonneg ‖polynomialSphereL2 (p k)‖)
  convert h using 1 <;> dsimp [x,d] <;> ring

private theorem polynomial_harmonic_hessian_zero_of_degree_lt_two {k : ℕ}
    (hk : k < 2) {p : MvPolynomial (Fin dim) ℝ} (hp : p ∈ harmonicHomogeneous dim k)
    (i j : Fin dim) : pderiv j (pderiv i p) = 0 := by
  rcases k with _ | _ | k
  · rw [pderiv_eq_zero_of_isHomogeneous_zero hp.1 i,map_zero]
  · exact pderiv_eq_zero_of_isHomogeneous_zero (harmonicHomogeneous_pderiv (k := 0) hp i).1 j
  · omega

private theorem harmonicHomogeneous_second_pderiv {k : ℕ}
    (hk : 2 ≤ k) {p : MvPolynomial (Fin dim) ℝ} (hp : p ∈ harmonicHomogeneous dim k) (i j : Fin dim) :
    pderiv j (pderiv i p) ∈ harmonicHomogeneous dim (k-2) := by
  have h : k - 2 + 1 + 1 = k := by omega
  exact harmonicHomogeneous_pderiv (harmonicHomogeneous_pderiv (h ▸ hp) i) j

private theorem integral_finite_harmonic_second_pderiv_sum_sq
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin dim) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous dim k) (i j : Fin dim) :
    (∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i (∑ k ∈ s, p k))) z ^ 2) =
      ∑ k ∈ s, ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i (p k))) z ^ 2 := by
  rw [map_sum,map_sum]
  apply integral_polynomialEvaluation_sum_sq
  intro k hk l hl hkl
  by_cases hK : k < 2
  · rw [polynomial_harmonic_hessian_zero_of_degree_lt_two hK (hp k hk) i j]
    simp [polynomialEvaluation]
  by_cases hL : l < 2
  · rw [polynomial_harmonic_hessian_zero_of_degree_lt_two hL (hp l hl) i j]
    simp [polynomialEvaluation]
  have hK' := harmonicHomogeneous_second_pderiv (by omega : 2 ≤ k) (hp k hk) i j
  have hL' := harmonicHomogeneous_second_pderiv (by omega : 2 ≤ l) (hp l hl) i j
  rw [integral_ball_polynomialEvaluation_mul hK'.1 hL'.1]
  rw [orthogonalSphereHarmonics dim (k-2) (l-2) (by omega)
    _ (polynomialSphereL2_mem _ _ hK') _ (polynomialSphereL2_mem _ _ hL'),mul_zero]

/-- The same native lift bound on all degrees, including the constant
and linear modes where the second derivative vanishes. -/
theorem norm_sq_all_finite_harmonic_H2_lift_le (s : Finset ℕ)
    (p : ℕ → MvPolynomial (Fin dim) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous dim k) :
    ‖polynomialBallSobolevL 2 (∑ k ∈ s, p k)‖^2 ≤
      ((dim : ℝ)+3)*unitSphereArea dim *
        ∑ k ∈ s, (1+(k : ℝ))^3*‖polynomialSphereL2 (p k)‖^2 := by
  let q := ∑ k ∈ s, p k
  let u : SmoothData dim := ⟨polynomialEvaluation q,contDiff_polynomialEvaluation q⟩
  let U := smoothSobolev u
  let A := unitSphereArea dim
  let H := ∑ k ∈ s, (1+(k : ℝ))^3*‖polynomialSphereL2 (p k)‖^2
  have hA : 0 ≤ A := (unitSphereArea_pos (dim := dim)).le
  have hVal : ‖TauCeti.W1p.value U‖^2 = ∫ z in ball (0 : X dim) 1, polynomialEvaluation q z ^ 2 := by
    rw [← TauCeti.W1p.integral_value_sq_eq_norm_value_sq]
    apply integral_congr_ae
    filter_upwards [value_smoothSobolev_ae u] with z hz
    rw [show TauCeti.W1p.value U z = polynomialEvaluation q z from hz]
  have hGrad : ‖TauCeti.W1p.gradient U‖^2 = ∫ z in ball (0 : X dim) 1, ‖gradient (polynomialEvaluation q) z‖^2 := by
    rw [← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae u] with z hz
    rw [show TauCeti.W1p.gradient U z = gradient (polynomialEvaluation q) z from hz]
  have h₁ : ‖U‖^2 ≤ A*H := by
    change ‖smoothSobolev u‖^2 ≤ _
    rw [← polynomialBallH1L_apply q]
    refine (norm_sq_finite_harmonic_polynomialBallH1_le s p hp).trans ?_
    apply mul_le_mul_of_nonneg_left _ hA
    apply Finset.sum_le_sum
    intro k hk
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h := one_le_pow₀ (show (1 : ℝ) ≤ 1+(k : ℝ) from by linarith [Nat.cast_nonneg (α := ℝ) k]) (n := 2)
    nlinarith only [mul_le_mul_of_nonneg_right h (show (0 : ℝ) ≤ 1+k from by positivity)]
  have h₂ : (∑ i : Fin dim, ∑ j : Fin dim,
        ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i q)) z ^ 2) ≤
      ((dim : ℝ)+2)*A*H := by
    have he (i j : Fin dim) : (∫ z in ball (0 : X dim) 1,
        polynomialEvaluation (pderiv j (pderiv i q)) z ^ 2) =
        ∑ k ∈ s, ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i (p k))) z ^ 2 :=
      integral_finite_harmonic_second_pderiv_sum_sq s p hp i j
    simp_rw [he]
    rw [Finset.sum_comm (f := fun (i j : Fin dim) => ∑ k ∈ s,
      ∫ z in ball (0 : X dim) 1, polynomialEvaluation (pderiv j (pderiv i (p k))) z ^ 2)]
    conv_lhs =>
      enter [2,j]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    change _ ≤ ((dim : ℝ)+2)*A* ∑ k ∈ s, (1+(k : ℝ))^3*‖polynomialSphereL2 (p k)‖^2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hK : k < 2
    · simp_rw [polynomial_harmonic_hessian_zero_of_degree_lt_two hK (hp k hk)]
      simp only [polynomialEvaluation,map_zero,zero_pow (by norm_num : 2 ≠ 0),integral_zero,Finset.sum_const_zero]
      positivity
    · obtain ⟨l,rfl⟩ : ∃ l : ℕ, k = l+2 := ⟨k-2,by omega⟩
      rw [Finset.sum_comm, sum_integral_ball_harmonic_second_pderiv_sq (l+1) (p (l+2)) (hp (l+2) hk)]
      let x : ℝ := l
      let d : ℝ := dim
      have hx : 0 ≤ x := Nat.cast_nonneg l
      have hd : 0 ≤ d := Nat.cast_nonneg dim
      have h : (x+1)*((x+2)*(2*(x+1)+d)) ≤ (d+2)*(x+3)^3 := by
        calc
          _ ≤ (x+3)*((x+3)*((d+2)*(x+3))) := by
            apply mul_le_mul (by linarith)
            · apply mul_le_mul (by linarith)
              · nlinarith only [mul_nonneg hd hx,hd]
              · positivity
              · positivity
            · positivity
            · positivity
          _ = _ := by ring
      have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hA)
        (sq_nonneg ‖polynomialSphereL2 (p (l+2))‖)
      push_cast
      convert h' using 1 <;> dsimp only [x,d,A] <;> ring
  rw [polynomialBallSobolevL_apply]
  refine (norm_sq_smoothBallSobolev_polynomialEvaluation_le q).trans ?_
  rw [← hVal,← hGrad,← TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  exact (add_le_add h₁ h₂).trans_eq (by dsimp only [A,H]; ring)

end CalderonN
