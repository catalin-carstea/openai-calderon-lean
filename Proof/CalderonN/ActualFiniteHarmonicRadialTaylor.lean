module

public import Proof.CalderonN.ActualPolynomialRadialTaylor
public import Proof.CalderonN.FiniteHarmonicH2Lift

import Proof.CalderonN.PolynomialBallSobolev

import Mathlib.Tactic

public section

noncomputable section
open Set Metric MvPolynomial
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The genuine fixed-ball radial trace minus the flat trace and its
explicit first correction has a uniform quadratic gain from finite
boundary (H^{3/2}) to boundary (H^{1/2}). -/
theorem uniform_actual_finite_harmonic_radial_taylor (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin dim) ℝ),
        (∀ k ∈ s, p k ∈ harmonicHomogeneous dim k) →
      let u := polynomialEvaluation (∑ k ∈ s, p k)
      let v := polynomialEvaluation (∑ k ∈ s,
        driftFirstVariation k (fun i => firstDensityCenterLinear d y (axis i)) (p k))
      ∃ b e : SmoothData dim,
        EqOn b.1 u (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z =>
          firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z)) b.1)
          0 (ball (0 : X dim) 1) ∧
        (∀ z, e.1 z = b.1 z-u z-d.radius y*v z) ∧
        ∀ t : Finset ℕ,
          let w := smoothBallRadialDerivative e
          (∑ j ∈ t, (1+(j : ℝ))*‖harmonicProjection j (smoothSphereLift w.1 w.2)‖^2) ≤
            B*(∑ k ∈ s, (1+(k : ℝ))^3*‖polynomialSphereL2 (p k)‖^2)*(d.radius y)^4 := by
  obtain ⟨F0,hF0,η,C,hη,hC,h⟩ :=
    uniform_actual_classical_normalizedPoisson_taylor (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  let D := ((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2
  let B := D*C^2*((dim : ℝ)+3)
  refine ⟨η,B,hη,by dsimp [B,D];positivity,?_⟩
  intro floor hf ε hε hεη d hd y hy s p hp
  let ℓ := firstDensityCenterLinear d y
  let q (k : ℕ) := driftFirstVariation k (fun i => ℓ (axis i)) (p k)
  let pS := ∑ k ∈ s, p k
  let qS := ∑ k ∈ s, q k
  let u : SmoothData dim := ⟨polynomialEvaluation pS,contDiff_polynomialEvaluation pS⟩
  let v : SmoothData dim := ⟨polynomialEvaluation qS,contDiff_polynomialEvaluation qS⟩
  have hH : EqOn (laplace (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1) := by
    intro z _
    change laplace (fun _ => (1 : Mat dim)) (polynomialEvaluation pS) z = 0
    rw [laplace_identity_polynomialEvaluation]
    have hzero : AngularPolynomial.laplacian pS = 0 := by
      unfold pS
      rw [laplacian_sum]
      exact Finset.sum_eq_zero (fun k hk => (hp k hk).2)
    rw [hzero]
    exact map_zero (eval (euclideanCoordinates dim z))
  obtain ⟨F1,hF1,hP⟩ := h floor hf ε hε hεη d hd y hy
  obtain ⟨b,hb,hT,hL,hB⟩ := hP u hH
  let bs : SmoothData dim := ⟨b,hb⟩
  let r := d.radius y
  let U : smoothBallDataSubmodule dim := ⟨u.1,u.2⟩
  let V : smoothBallDataSubmodule dim := ⟨v.1,v.2⟩
  let E : smoothBallDataSubmodule dim := ⟨b,hb⟩-U-r • V
  let e : SmoothData dim := ⟨E,smoothBallData_contDiff E⟩
  let j := (strongDirichletSubmodule dim 0).toSubmodule.subtypeL
  let I₀ := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
  let Q := -(j.comp (I₀.comp (fullBallDivergenceL 0 F1)))
  have hFirst : smoothBallSobolev 2 v = Q (smoothBallSobolev 2 u) := by
    rw [show smoothBallSobolev 2 v = polynomialBallSobolevL 2 qS from (polynomialBallSobolevL_apply 2 qS).symm,
      show smoothBallSobolev 2 u = polynomialBallSobolevL 2 pS from (polynomialBallSobolevL_apply 2 pS).symm]
    simp only [pS,qS,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [polynomialBallSobolevL_apply,polynomialBallSobolevL_apply]
    exact polynomialFirstVariation_represents_strongInverse F0 F1 hF0 ℓ hF1 k (p k) (hp k hk)
  have hEq : smoothBallSobolev 2 e = smoothBallSobolev 2 bs-smoothBallSobolev 2 u-r • smoothBallSobolev 2 v := by
    change smoothBallSobolevLinear dim 2 E =
      smoothBallSobolevLinear dim 2 (⟨b,hb⟩ : smoothBallDataSubmodule dim)-
      smoothBallSobolevLinear dim 2 U-r • smoothBallSobolevLinear dim 2 V
    simp only [E,map_sub,map_smul]
  have hNorm : ‖smoothBallSobolev 2 e‖ ≤ C * ‖smoothBallSobolev 2 u‖ * r^2 := by
    rw [hEq,hFirst]
    exact hB
  refine ⟨bs,e,hT,hL,fun _ => rfl,?_⟩
  intro t
  have hSq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hNorm
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hH2 := norm_sq_all_finite_harmonic_H2_lift_le s p hp
  rw [polynomialBallSobolevL_apply] at hH2
  have hES := (sum_sharpBallRadialTrace_le e t).trans (mul_le_mul_of_nonneg_left hSq hD)
  let w := smoothBallRadialDerivative e
  let W := ∑ k ∈ s, (1+(k : ℝ))^3*‖polynomialSphereL2 (p k)‖^2
  change unitSphereArea dim * (∑ i ∈ t, (1+(i : ℝ))*‖harmonicProjection i
    (smoothSphereLift w.1 w.2)‖^2) ≤ D * (C*‖smoothBallSobolev 2 u‖*r^2)^2 at hES
  change ‖smoothBallSobolev 2 u‖^2 ≤ ((dim : ℝ)+3)*unitSphereArea dim*W at hH2
  apply le_of_mul_le_mul_left _ (unitSphereArea_pos (dim := dim))
  calc
    _ ≤ D * (C*‖smoothBallSobolev 2 u‖*r^2)^2 := hES
    _ = (D*C^2*r^4)*‖smoothBallSobolev 2 u‖^2 := by ring
    _ ≤ (D*C^2*r^4)*(((dim : ℝ)+3)*unitSphereArea dim*W) :=
      mul_le_mul_of_nonneg_left hH2 (by positivity)
    _ = unitSphereArea dim * (B*W*r^4) := by dsimp [B]; ring

end CalderonN
