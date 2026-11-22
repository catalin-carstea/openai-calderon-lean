module

public import Proof.CalderonN.ActualStrongAngularCorrection
public import Proof.CalderonN.ActualFiniteRadialEndpoints

import Mathlib.Tactic

/-! The strong angular correction has the half-order radial trace bound
on the common finite boundary coefficient space. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff DirectSum Classical
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation GreenRadialTrace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem norm_sq_finite_harmonic_H2_smooth_le (f : HarmonicFiniteCoefficients dim) :
    ‖smoothBallSobolev 2 (harmonicFiniteSmooth f)‖^2 ≤
      ((dim : ℝ)+3)*unitSphereArea dim*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖^2 := by
  let p (k : ℕ) := harmonicPolynomialRepresentativeL k (f k)
  have h := norm_sq_all_finite_harmonic_H2_lift_le f.support p
    (fun k _ => harmonicPolynomialRepresentative_mem k (f k))
  rw [polynomialBallSobolevL_apply] at h
  change ‖smoothBallSobolev 2 (harmonicFiniteSmooth f)‖^2 ≤ _ at h
  rw [harmonicBoundaryFiniteL_eq_sum,norm_sq_finite_boundary_sum]
  simpa only [p,polynomialSphereL2_harmonicPolynomialRepresentative,besselWeight_three_halves_sq,
    Submodule.coe_norm] using h

theorem uniform_actual_strong_angular_radial (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      ∀ i j : Fin dim, ∀ f : HarmonicFiniteCoefficients dim,
        let u := harmonicFiniteSmooth f
        let qθ := harmonicFiniteDriftVariationSmooth (ell.comp (ballRotationGeneratorL i j)) f
        ∃ b bθ R : SmoothData dim,
          EqOn b.1 u.1 (standardSphere dim) ∧
          EqOn bθ.1 (sphereRotationDerivative i j u.1) (standardSphere dim) ∧
          EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
          EqOn (negativeBallDivergence a bθ.1) 0 (ball (0 : X dim) 1) ∧
          (∀ z, R.1 z = sphereRotationDerivative i j (fun w => fderiv ℝ b.1 w w) z-
            fderiv ℝ bθ.1 z z-r*fderiv ℝ qθ.1 z z) ∧
          ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) R‖ ≤
            B*r^2*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖ := by
  obtain ⟨η,C,hη,hC,h⟩ := uniform_actual_strong_angular_correction (Y := Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  let D := ((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2
  let B := Real.sqrt (D*C^2*((dim : ℝ)+3))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨η,B,hη,Real.sqrt_nonneg _,?_⟩
  intro floor hf ε hε hεη d hd y hy
  dsimp only
  intro i j f
  let r := d.radius y
  let u := harmonicFiniteSmooth f
  let ellθ := (firstDensityCenterLinear d y).comp (ballRotationGeneratorL i j)
  let qθ := harmonicFiniteDriftVariationSmooth ellθ f
  obtain ⟨b,bθ,e,hbT,hbθT,hbH,hbθH,he,hEN⟩ := h floor hf ε hε hεη d hd y hy i j f
  let R := smoothBallRadialDerivative e
  refine ⟨b,bθ,R,hbT,hbθT,hbH,hbθH,?_,?_⟩
  · intro z
    let w := angularBallCorrection i j b bθ
    have he' : e.1 = w.1-r • qθ.1 := funext he
    change fderiv ℝ e.1 z z = _
    have hSub := fderiv_sub (w.2.differentiable (by simp) z)
      (qθ.2.const_smul r |>.differentiable (by simp) z)
    change fderiv ℝ (w.1-r • qθ.1) z = fderiv ℝ w.1 z-fderiv ℝ (r • qθ.1) z at hSub
    rw [he',hSub,sub_apply,angularBallCorrection_radialDerivative]
    have hE : fderiv ℝ (r • qθ.1) z = r • fderiv ℝ qθ.1 z :=
      fderiv_const_smul (qθ.2.differentiable (by simp) z) r
    rw [hE,smul_apply,smul_eq_mul]
  let L := harmonicBoundaryFiniteL (dim := dim) (3/2 : ℝ)
  have hB0 : 0 ≤ D*C^2*((dim : ℝ)+3) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ B*r^2*‖L f‖)).mp
  apply sq_smoothBoundarySobolev_half_of_truncations hn
  intro t
  have hTrace := sum_sharpBallRadialTrace_le e t
  have hu := norm_sq_finite_harmonic_H2_smooth_le f
  have he2 : ‖smoothBallSobolev 2 e‖^2 ≤ (C*r^2*‖smoothBallSobolev 2 u‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hEN
  have hArea : 0 < unitSphereArea dim := unitSphereArea_pos
  apply le_of_mul_le_mul_left _ hArea
  calc
    _ ≤ D*‖smoothBallSobolev 2 e‖^2 := hTrace
    _ ≤ D*(C*r^2*‖smoothBallSobolev 2 u‖)^2 := mul_le_mul_of_nonneg_left he2 hD
    _ = (D*C^2*r^4)*‖smoothBallSobolev 2 u‖^2 := by ring
    _ ≤ (D*C^2*r^4)*(((dim : ℝ)+3)*unitSphereArea dim*‖L f‖^2) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = unitSphereArea dim*(B*r^2*‖L f‖)^2 := by
      rw [mul_pow,mul_pow,show B^2 = D*C^2*((dim : ℝ)+3) from Real.sq_sqrt hB0]
      ring

end CalderonN
