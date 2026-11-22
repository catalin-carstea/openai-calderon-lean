module

public import Proof.CalderonN.ActualFiniteWeakRadialTaylor
public import Proof.CalderonN.ActualFiniteHarmonicRadialTaylor
public import Proof.CalderonN.FixedBallFluxUnique

import Proof.CalderonN.NormalizedStrongPoissonTaylor
import Mathlib.Tactic

/-! Weak and strong finite-harmonic radial estimates for the same
normalized classical solution. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise Classical DirectSum
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SphereHarmonic

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem besselWeight_three_halves_sq (k : ℕ) :
    besselWeight (3/2 : ℝ) k ^ 2 = (1+(k : ℝ))^3 := by
  rw [besselWeight_square,show (2 : ℝ)*(3/2) = 3 by norm_num]
  norm_num

omit [Nontrivial (Fin dim)] in
theorem sq_smoothBoundarySobolev_half_of_truncations (hn : 3 ≤ dim)
    (u : SmoothData dim) (B : ℝ)
    (h : ∀ s : Finset ℕ, (∑ k ∈ s, (1+(k : ℝ))*‖harmonicProjection k (smoothSphereLift u.1 u.2)‖^2) ≤ B) :
    ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u‖^2 ≤ B := by
  let U := smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u
  have hT := (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) U).tendsto_sum_nat
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hT
  apply le_of_tendsto_of_tendsto' hT tendsto_const_nhds
  intro k
  simpa only [U,smoothBoundarySobolev_apply,norm_smul,Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos _ _),mul_pow,besselWeight_one_half_sq] using h (Finset.range k)

/-- For every finite harmonic datum the same smooth radial remainder has
both quadratic endpoint estimates, uniformly in the ambient dimension
once the dimension is fixed. -/
theorem uniform_actual_finite_radial_endpoints (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ, 0 < η ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let A (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      ∃ a : X dim → Mat dim, ContDiff ℝ ∞ a ∧ EqOn a A (ball (0 : X dim) 1) ∧
        (∃ lo hi, UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi) ∧
        ∀ f : HarmonicFiniteCoefficients dim,
          let u := harmonicFiniteSmooth f
          let q := harmonicFiniteDriftVariationSmooth ell f
          ∃ b E : SmoothData dim,
            EqOn b.1 u.1 (standardSphere dim) ∧
            EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1) ∧
            (∀ z, E.1 z = fderiv ℝ b.1 z z-fderiv ℝ u.1 z z-r*fderiv ℝ q.1 z z) ∧
            ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) E‖ ≤
              C0*r^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ ∧
            ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) E‖ ≤
              C1*r^2*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖ := by
  obtain ⟨η0,C0,hη0,hC0,h0⟩ := uniform_actual_finite_weak_radial_taylor (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η1,C1,hη1,hC1,h1⟩ := uniform_actual_finite_harmonic_radial_taylor (Y := Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨_,_,ηA,_,hηA,_,hA⟩ := uniform_normalized_fixedBall_poisson_first_variation (Y := Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min η0 (min η1 ηA),C0,Real.sqrt C1,lt_min hη0 (lt_min hη1 hηA),hC0,Real.sqrt_nonneg _,?_⟩
  intro floor hf ε hε hsmall d hd y hy
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  let A (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  obtain ⟨F,_,hF,_,⟨lo,hi,hEll⟩,_⟩ := hA floor hf ε hε
    (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy
  let a := coefficientMatrixField 2 F
  have ha := contDiff_coefficientMatrixField 2 F
  have hA' : EqOn a A (ball (0 : X dim) 1) := hF.mono (ball_subset_ball (by norm_num))
  refine ⟨a,ha,hA',⟨lo,hi,hEll⟩,?_⟩
  intro f
  obtain ⟨b,E,hbT,hbH,hE,hLow⟩ := h0 floor hf ε hε (hsmall.trans (min_le_left _ _)) d hd y hy f
  let p (k : ℕ) := harmonicPolynomialRepresentativeL k (f k)
  obtain ⟨b',E',hb'T,hb'H,hE',hHigh⟩ := h1 floor hf ε hε
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy f.support p
    (fun k _ => harmonicPolynomialRepresentative_mem k (f k))
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth ell f
  have ht : EqOn b.1 b'.1 (standardSphere dim) := by
    intro z hz
    have h : b'.1 z = u.1 z := hb'T hz
    exact (hbT hz).trans h.symm
  have hR := eqOn_radialDerivative_of_classicalNormalResponses ha hEll hA' b b' hbH hb'H ht
  have hEO (z : X dim) : E'.1 z = b'.1 z-u.1 z-r*q.1 z := hE' z
  let R' := smoothBallRadialDerivative E'
  have hEr : EqOn E.1 R'.1 (standardSphere dim) := by
    intro z hz
    rw [hE z]
    have hh : fderiv ℝ b.1 z z = fderiv ℝ b'.1 z z := hR hz
    rw [hh]
    change fderiv ℝ b'.1 z z-fderiv ℝ u.1 z z-r*fderiv ℝ q.1 z z = fderiv ℝ E'.1 z z
    have hDiff : DifferentiableAt ℝ (fun x => b'.1 x-u.1 x) z :=
      (b'.2.differentiable (by simp) z).sub (u.2.differentiable (by simp) z)
    have hDiff' : DifferentiableAt ℝ (fun x => r*q.1 x) z :=
      (differentiableAt_const r).mul (q.2.differentiable (by simp) z)
    rw [show E'.1 = (fun x => b'.1 x-u.1 x-r*q.1 x) from funext hEO,
      fderiv_fun_sub hDiff hDiff',
      fderiv_fun_sub (b'.2.differentiable (by simp) z) (u.2.differentiable (by simp) z)]
    have hQ : fderiv ℝ (fun x => r*q.1 x) z = r • fderiv ℝ q.1 z := by
      change fderiv ℝ (r • q.1) z = _
      exact fderiv_const_smul (q.2.differentiable (by simp) z) r
    rw [hQ,sub_apply,sub_apply,smul_apply,smul_eq_mul]
  refine ⟨b,E,hbT,hbH,hE,hLow,?_⟩
  rw [smoothBoundarySobolev_eq_of_eqOn hn (1/2 : ℝ) (by norm_num) E R' hEr]
  have hSum (t : Finset ℕ) :
      (∑ j ∈ t, (1+(j : ℝ))*‖harmonicProjection j (smoothSphereLift R'.1 R'.2)‖^2) ≤
        C1*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖^2*r^4 := by
    have h := hHigh t
    rw [harmonicBoundaryFiniteL_eq_sum,norm_sq_finite_boundary_sum]
    simpa only [p,polynomialSphereL2_harmonicPolynomialRepresentative,besselWeight_three_halves_sq,
      Submodule.coe_norm,R',r] using h
  have hh := sq_smoothBoundarySobolev_half_of_truncations hn R' _ hSum
  have he : (Real.sqrt C1*r^2*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖)^2 =
      C1*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖^2*r^4 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hC1]
    ring
  rw [← he] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hh

end CalderonN
