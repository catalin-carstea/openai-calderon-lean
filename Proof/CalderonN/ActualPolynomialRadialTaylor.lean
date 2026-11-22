module

public import Proof.CalderonN.ActualClassicalPoissonTaylor
public import Proof.CalderonN.PolynomialPoissonFirstVariation
public import Proof.CalderonN.SharpBallRadialTrace

import Mathlib.Tactic

public section

noncomputable section
open Set Metric MvPolynomial
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- On a solid harmonic, the actual radial trace has the released
explicit affine drift variation and a uniform quadratic remainder in the
half-order boundary energy. -/
theorem uniform_actual_polynomial_radial_taylor (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ k (p : MvPolynomial (Fin dim) ℝ), p ∈ harmonicHomogeneous dim k →
      let u : SmoothData dim := ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
      let q := driftFirstVariation k (fun i => firstDensityCenterLinear d y (axis i)) p
      let v : SmoothData dim := ⟨polynomialEvaluation q,contDiff_polynomialEvaluation q⟩
      ∃ b e : SmoothData dim,
        EqOn b.1 u.1 (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z =>
          firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z)) b.1)
          0 (ball (0 : X dim) 1) ∧
        (∀ z, e.1 z = b.1 z-u.1 z-d.radius y*v.1 z) ∧
        ∀ s : Finset ℕ,
          let w := smoothBallRadialDerivative e
          unitSphereArea dim * ∑ j ∈ s, (1+(j : ℝ)) *
            ‖harmonicProjection j (smoothSphereLift w.1 w.2)‖^2 ≤
            B * ‖smoothBallSobolev 2 u‖^2 * (d.radius y)^4 := by
  obtain ⟨F0,hF0,η,C,hη,hC,h⟩ :=
    uniform_actual_classical_normalizedPoisson_taylor (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  let D := ((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2
  refine ⟨η,D*C^2,hη,by dsimp [D];positivity,?_⟩
  intro floor hf ε hε hεη d hd y hy k p hp
  let u : SmoothData dim := ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
  let q := driftFirstVariation k (fun i => firstDensityCenterLinear d y (axis i)) p
  let v : SmoothData dim := ⟨polynomialEvaluation q,contDiff_polynomialEvaluation q⟩
  have hH : EqOn (laplace (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    change laplace (fun _ => (1 : Mat dim)) (polynomialEvaluation p) z = 0
    rw [laplace_identity_polynomialEvaluation,hp.2]
    exact map_zero (eval (euclideanCoordinates dim z))
  obtain ⟨F1,hF1,hP⟩ := h floor hf ε hε hεη d hd y hy
  obtain ⟨b,hb,hT,hL,hB⟩ := hP u hH
  let bs : SmoothData dim := ⟨b,hb⟩
  let r := d.radius y
  let U : smoothBallDataSubmodule dim := ⟨u.1,u.2⟩
  let V : smoothBallDataSubmodule dim := ⟨v.1,v.2⟩
  let E : smoothBallDataSubmodule dim := ⟨b,hb⟩-U-r • V
  let e : SmoothData dim := ⟨E,smoothBallData_contDiff E⟩
  have hp' := polynomialFirstVariation_represents_strongInverse F0 F1 hF0
    (firstDensityCenterLinear d y) hF1 k p hp
  change smoothBallSobolev 2 v = -((strongDirichletSubmodule dim 0).toSubmodule.subtypeL)
    ((strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
      (fullBallDivergenceL 0 F1 (smoothBallSobolev 2 u))) at hp'
  have hEq : smoothBallSobolev 2 e = smoothBallSobolev 2 bs-smoothBallSobolev 2 u-r • smoothBallSobolev 2 v := by
    change smoothBallSobolevLinear dim 2 E =
      smoothBallSobolevLinear dim 2 (⟨b,hb⟩ : smoothBallDataSubmodule dim)-
      smoothBallSobolevLinear dim 2 U-r • smoothBallSobolevLinear dim 2 V
    simp only [E,map_sub,map_smul]
  have hNorm : ‖smoothBallSobolev 2 e‖ ≤ C * ‖smoothBallSobolev 2 u‖ * r^2 := by
    rw [hEq,hp']
    exact hB
  refine ⟨bs,e,hT,hL,fun z => rfl,?_⟩
  intro s
  have hSq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hNorm
  have hD : 0 ≤ D := by dsimp [D]; positivity
  exact ((sum_sharpBallRadialTrace_le e s).trans (mul_le_mul_of_nonneg_left hSq hD)).trans_eq
    (by ring)

end CalderonN
