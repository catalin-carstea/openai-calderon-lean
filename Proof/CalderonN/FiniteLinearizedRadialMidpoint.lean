module

public import Proof.CalderonN.FiniteLinearizedRadialLinear
public import Proof.CalderonN.ActualAngularRadialMidpoint

import Mathlib.Tactic

/-! The two endpoint estimates concern one linearized response. Their
interpolation gives the quadratic estimate for the radial derivative. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise DirectSum Classical
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic GreenRadialTrace
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

private theorem norm_smoothBallRadialDerivative_high_le (hn : 3 ≤ dim)
    (f : HarmonicFiniteCoefficients dim) (e : SmoothData dim) {C r : ℝ} (hC : 0 ≤ C)
    (hE : ‖smoothBallSobolev 2 e‖ ≤ C*r^2*‖smoothBallSobolev 2 (harmonicFiniteSmooth f)‖) :
    ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (smoothBallRadialDerivative e)‖ ≤
      Real.sqrt (((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2*C^2*((dim : ℝ)+3))*
        r^2*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖ := by
  let D := ((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2
  let B := Real.sqrt (D*C^2*((dim : ℝ)+3))
  let L := harmonicBoundaryFiniteL (dim := dim) (3/2 : ℝ)
  change ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (smoothBallRadialDerivative e)‖ ≤
    B*r^2*‖L f‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB0 : 0 ≤ D*C^2*((dim : ℝ)+3) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ B*r^2*‖L f‖)).mp
  apply sq_smoothBoundarySobolev_half_of_truncations hn
  intro t
  have hTrace := sum_sharpBallRadialTrace_le e t
  have hu := norm_sq_finite_harmonic_H2_smooth_le f
  have he2 : ‖smoothBallSobolev 2 e‖^2 ≤ (C*r^2*‖smoothBallSobolev 2 (harmonicFiniteSmooth f)‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hE
  have hArea : 0 < unitSphereArea dim := unitSphereArea_pos
  apply le_of_mul_le_mul_left _ hArea
  calc
    _ ≤ D*‖smoothBallSobolev 2 e‖^2 := hTrace
    _ ≤ D*(C*r^2*‖smoothBallSobolev 2 (harmonicFiniteSmooth f)‖)^2 :=
      mul_le_mul_of_nonneg_left he2 hD
    _ = (D*C^2*r^4)*‖smoothBallSobolev 2 (harmonicFiniteSmooth f)‖^2 := by ring
    _ ≤ (D*C^2*r^4)*(((dim : ℝ)+3)*unitSphereArea dim*‖L f‖^2) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = unitSphereArea dim*(B*r^2*‖L f‖)^2 := by
      rw [mul_pow,mul_pow,show B^2 = D*C^2*((dim : ℝ)+3) from Real.sq_sqrt hB0]
      ring

theorem uniform_finite_linearized_radial_midpoint (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      ∀ (ell : X dim →L[ℝ] ℝ) (G : X dim → Mat dim),
        ContDiff ℝ ∞ G → ‖ell‖ ≤ 2*P →
        (∀ z ∈ standardSphere dim, IsRadialRow z (G z)) →
        (∀ z ∈ closedBall (0 : X dim) 1, let R := G-r • (fun z => ell z • (1 : Mat dim))
          ‖R z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ R z‖ ≤ Q*r^2) →
      ∀ f : HarmonicFiniteCoefficients dim,
        let q := harmonicFiniteDriftVariationSmooth ell f
        ∃ b w R : SmoothData dim,
          EqOn b.1 (harmonicFiniteSmooth f).1 (standardSphere dim) ∧
          EqOn w.1 0 (standardSphere dim) ∧
          EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
          (∀ z ∈ ball (0 : X dim) 1,
            negativeBallDivergence a w.1 z = -negativeBallDivergence G b.1 z) ∧
          (∀ z, R.1 z = fderiv ℝ w.1 z z-r*fderiv ℝ q.1 z z) ∧
          ‖smoothBoundarySobolev hn 0 (by norm_num) R‖ ≤ B*r^2*‖harmonicBoundaryFiniteL 1 f‖ := by
  obtain ⟨η,H,C₀,hη,hH,hC₀,hWeak⟩ := uniform_finite_linearized_weak_radial (Y:=Y)
    hn hΩ hm K ρ c₀ M Cj hK hρ P Q hP hQ
  let C₁ := Real.sqrt (((dim : ℝ)+3)*‖ballRadialDerivativeL dim‖^2*H^2*((dim : ℝ)+3))
  have hC₁ : 0 ≤ C₁ := Real.sqrt_nonneg _
  refine ⟨η,(C₀+C₁)/2,hη,by positivity,?_⟩
  intro floor hf ε he hes d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  intro ell G hG hEll hRow hRem
  obtain ⟨A,hA,hAa,hApos,hResp⟩ := hWeak floor hf ε he hes d hd y hy
  obtain ⟨lo,hi,hPos⟩ := exists_uniformEllipticOn_fixedBall A hA.continuous hApos
  choose b w e R₀ hbT hwT hbH hwH heq heN hR₀ hRN using hResp ell G hG hEll hRow hRem
  have hGerm (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] a := by
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5/4) hz)]
      with x hx using hAa hx
  have hbH' (f : HarmonicFiniteCoefficients dim) :
      EqOn (negativeBallDivergence A (b f).1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    rw [negativeBallDivergence_congr_germ (hGerm z hz) EventuallyEq.rfl]
    exact hbH f hz
  have hwH' (f : HarmonicFiniteCoefficients dim) (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      negativeBallDivergence A (w f).1 z = -negativeBallDivergence G (b f).1 z := by
    rw [negativeBallDivergence_congr_germ (hGerm z hz) EventuallyEq.rfl]
    exact hwH f z hz
  let D := (smoothBallRadialDataL (dim := dim)).comp (harmonicFiniteDriftVariationSmoothL ell)
  let Z (s : ℝ) (hs : s ≤ 2) :=
    finiteLinearizedRadialResponseL hn s hs hA hG hPos b w hbT hwT hbH' hwH' -
      r • (smoothBoundarySobolevLinear hn s hs).comp D
  let asS (u : SmoothData dim) : smoothBallDataSubmodule dim := ⟨u.1,u.2⟩
  let R' (f : HarmonicFiniteCoefficients dim) := smoothBallRadialDataL (asS (w f))-r • D f
  let R (f : HarmonicFiniteCoefficients dim) : SmoothData dim := ⟨(R' f).1,smoothBallData_contDiff (R' f)⟩
  have hR (f : HarmonicFiniteCoefficients dim) (z : X dim) :
      (R f).1 z = fderiv ℝ (w f).1 z z-r*fderiv ℝ (harmonicFiniteDriftVariationSmooth ell f).1 z z := by
    change (smoothBallRadialDataL (asS (w f))).1 z-r*(D f).1 z = _
    rw [show (D f).1 = (smoothBallRadialDataL (harmonicFiniteDriftVariationSmoothL ell f)).1 from rfl,
      smoothBallRadialDataL_val,smoothBallRadialDataL_val,harmonicFiniteDriftVariationSmoothL_val]
  have hZ (s : ℝ) (hs : s ≤ 2) (f : HarmonicFiniteCoefficients dim) :
      Z s hs f = smoothBoundarySobolev hn s hs (R f) := by
    rw [show smoothBoundarySobolev hn s hs (R f) = smoothBoundarySobolevLinear hn s hs (R' f) from
      (smoothBoundarySobolevLinear_apply hn s hs (R' f)).symm]
    simp only [Z,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,
      finiteLinearizedRadialResponseL_apply,R',map_sub,map_smul,smoothBoundarySobolevLinear_apply]
    rfl
  have hLo (f : HarmonicFiniteCoefficients dim) :
      ‖Z (-1/2 : ℝ) (by norm_num) f‖ ≤ C₀*r^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
    have hEq : EqOn (R f).1 (R₀ f).1 (standardSphere dim) :=
      fun z _ => (hR f z).trans (hR₀ f z).symm
    rw [hZ,smoothBoundarySobolev_eq_of_eqOn hn _ (by norm_num) _ _ hEq]
    have hx : (-1/2 : ℝ) = -(1/2 : ℝ) := by ring
    rw [smoothBoundarySobolev_order_eq hn hx _ (by norm_num)]
    exact hRN f
  have hHi (f : HarmonicFiniteCoefficients dim) :
      ‖Z (1/2 : ℝ) (by norm_num) f‖ ≤ C₁*r^2*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖ := by
    have hEq : EqOn (R f).1 (smoothBallRadialDerivative (e f)).1 (standardSphere dim) := by
      intro z _
      rw [hR]
      let q := harmonicFiniteDriftVariationSmooth ell f
      have h : (e f).1 = (w f).1-r • q.1 := funext (heq f)
      change _ = fderiv ℝ (e f).1 z z
      have hSub := fderiv_sub ((w f).2.differentiable (by simp) z)
        ((q.2.const_smul r).differentiable (by simp) z)
      change fderiv ℝ ((w f).1-r • q.1) z = fderiv ℝ (w f).1 z-fderiv ℝ (r • q.1) z at hSub
      have hScale : fderiv ℝ (r • q.1) z = r • fderiv ℝ q.1 z :=
        fderiv_const_smul (q.2.differentiable (by simp) z) r
      rw [h,hSub,hScale,sub_apply,smul_apply,smul_eq_mul]
    rw [hZ,smoothBoundarySobolev_eq_of_eqOn hn _ (by norm_num) _ _ hEq]
    exact norm_smoothBallRadialDerivative_high_le hn f (e f) hH (heN f)
  intro f
  refine ⟨b f,w f,R f,hbT f,hwT f,hbH f,hwH f,hR f,?_⟩
  have hMid : ‖Z 0 (by norm_num) f‖ ≤ ((C₀*r^2+C₁*r^2)/2)*‖harmonicBoundaryFiniteL 1 f‖ := by
    refine norm_finiteSphere_midpoint_le
      (Z (-1/2 : ℝ) (by norm_num)) (Z 0 (by norm_num)) (Z (1/2 : ℝ) (by norm_num))
      ?_ ?_ (C₀*r^2) (C₁*r^2) (by positivity) (by positivity) hLo hHi f
    · intro g
      rw [hZ 0,hZ (-1/2 : ℝ)]
      exact sphereSobolevInclusionL_smoothBoundarySobolev hn 0 (-1/2 : ℝ) _ _ _ (R g)
    · intro g
      rw [hZ (1/2 : ℝ),hZ (-1/2 : ℝ)]
      exact sphereSobolevInclusionL_smoothBoundarySobolev hn (1/2 : ℝ) (-1/2 : ℝ) _ _ _ (R g)
  rw [hZ] at hMid
  exact hMid.trans_eq (by ring)

end CalderonN
