module

public import Proof.CalderonN.FiniteLinearizedRadialMidpoint
public import Proof.CalderonN.RelativeRadiusCoefficientJets

import Mathlib.Tactic

/-! The derivative in relative radius uses the true dilated coefficient,
with the same affine model as the original radial response. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3550000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def actualRelativeRadiusCoefficientDerivative (d : Data dim) (y z : X dim) : Mat dim :=
  deriv (fun t => relativeRadiusCoefficient d y t z) 0

theorem eqOn_ballDilationCoefficient_actual (d : Data dim) (y : X dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hEq : EqOn A (fun z => firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z))
      (ball (0 : X dim) (5/4))) :
    EqOn (ballDilationCoefficient A) (actualRelativeRadiusCoefficientDerivative d y)
      (ball (0 : X dim) (5/4)) := by
  intro z hz
  let F (t : ℝ) := (1+t) • z
  have h₀ : F 0 = z := by simp [F]
  have hF : HasDerivAt F z 0 := by
    simpa only [F,id_eq,one_smul] using (((hasDerivAt_id (0:ℝ)).const_add 1).smul_const z)
  have hD := (show HasFDerivAt A (fderiv ℝ A z) (F 0) by
    rw [h₀]; exact (hA.differentiable (by simp) z).hasFDerivAt).comp_hasDerivAt 0 hF
  have hNear : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), F t ∈ ball (0 : X dim) (5/4) :=
    hF.continuousAt.eventually (isOpen_ball.mem_nhds (h₀ ▸ hz))
  have hSame : (fun t => relativeRadiusCoefficient d y t z) =ᶠ[𝓝 (0:ℝ)] A ∘ F := by
    filter_upwards [hNear] with t ht
    change relativeRadiusCoefficient d y t z = A (F t)
    rw [hEq ht]
    change relativeRadiusCoefficient d y t z =
      firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y ((1+t) • z))
    rw [← frameVectorLinear_apply,map_smul,smul_smul,frameVectorLinear_apply]
    rfl
  exact (hD.congr_of_eventuallyEq hSame).deriv.symm

theorem uniform_actual_relative_radius_radial_response (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let A (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let G := actualRelativeRadiusCoefficientDerivative d y
      let ell := firstDensityCenterLinear d y
      ∀ f : HarmonicFiniteCoefficients dim,
        let q := harmonicFiniteDriftVariationSmooth ell f
        ∃ b w R : SmoothData dim,
          EqOn b.1 (harmonicFiniteSmooth f).1 (standardSphere dim) ∧
          EqOn w.1 0 (standardSphere dim) ∧
          EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1) ∧
          (∀ z ∈ ball (0 : X dim) 1,
            negativeBallDivergence A w.1 z = -negativeBallDivergence G b.1 z) ∧
          (∀ z, R.1 z = fderiv ℝ w.1 z z-r*fderiv ℝ q.1 z z) ∧
          ‖smoothBoundarySobolev hn 0 (by norm_num) R‖ ≤ B*r^2*‖harmonicBoundaryFiniteL 1 f‖ := by
  obtain ⟨ηL,P,hηL,hP,hEll⟩ := uniform_actual_radial_weight_remainder (Y:=Y) (by omega : 2 ≤ dim)
    hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηG,Q,hηG,hQ,hJet⟩ := uniform_relativeRadius_coefficient_jet (Y:=Y) (by omega : 2 ≤ dim)
    hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,_,_,hηA,_,_,hLifts⟩ := uniform_normalized_coefficient_lifts (Y:=Y) (by omega : 2 ≤ dim)
    hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,B,hηR,hB,hR⟩ := uniform_finite_linearized_radial_midpoint (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
    P Q hP hQ
  obtain ⟨F0,hF0⟩ := exists_flatCoefficientMatrix dim 2
  let η := min (min ηA ηG) (min ηL (min ηR (ρ/2)))
  refine ⟨η,B,lt_min (lt_min hηA hηG) (lt_min hηL (lt_min hηR (by positivity))),hB,?_⟩
  intro floor hf ε he hε d hd y hy
  dsimp only
  intro f
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  obtain ⟨F,_,hF,_,_,_,_,_,_⟩ := hLifts F0 hF0 floor hf ε he
    (hε.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  let A := coefficientMatrixField 2 F
  let G := ballDilationCoefficient A
  have hA := contDiff_coefficientMatrixField 2 F
  have hG := contDiff_ballDilationCoefficient hA
  have hReal := eqOn_ballDilationCoefficient_actual d y hA hF
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hre : r ≤ ε := (le_mul_of_one_le_right hr.le
    (one_le_pow₀ (hf.trans (hd.2.2.2.2.1.2 y hy).2.1))).trans (hd.2.2.2.2.2 y hy).2
  have hrρ : r < ρ := (hre.trans (hε.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))).trans_lt (half_lt_self hρ)
  have hRow (z : X dim) (hz : z ∈ standardSphere dim) : IsRadialRow z (G z) :=
    isRadialRow_ballDilationCoefficient (by omega : 2 ≤ dim) hΩ hd (zero_lt_one.trans_le hK)
      hy hrρ hz hA hF
  have hℓ : ‖ell‖ ≤ P := (hEll floor hf ε he
    (hε.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy).1
  have hRem := hJet floor hf ε he (hε.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy
  have hGerm (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) :
      G =ᶠ[𝓝 z] actualRelativeRadiusCoefficientDerivative d y := by
    filter_upwards [isOpen_ball.mem_nhds (closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4) hz)]
      with w hw using hReal hw
  have hRem' (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) :
      let E := G-r • (fun z => ell z • (1 : Mat dim))
      ‖E z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ E z‖ ≤ Q*r^2 := by
    let E := G-r • (fun z => ell z • (1 : Mat dim))
    let S (z : X dim) := deriv (fun t => relativeRadiusCoefficient d y t z) 0 -
      (r*ell z) • (1 : Mat dim)
    have hER : E =ᶠ[𝓝 z] S := by
      filter_upwards [hGerm z hz] with w hw
      simp only [E,S,Pi.sub_apply,Pi.smul_apply,hw,smul_smul,actualRelativeRadiusCoefficientDerivative]
    change ‖E z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ E z‖ ≤ Q*r^2
    rw [hER.eq_of_nhds,hER.fderiv_eq]
    exact (hRem z (closedBall_subset_ball (by norm_num : (1:ℝ) < 2) hz)).2
  obtain ⟨b,w,S,hbT,hwT,hbH,hwH,hSe,hSn⟩ := hR floor hf ε he
    (hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) d hd y hy
    ell G hG (hℓ.trans (by linarith)) hRow hRem' f
  refine ⟨b,w,S,hbT,hwT,hbH,?_,hSe,hSn⟩
  intro z hz
  rw [← negativeBallDivergence_congr_germ (hGerm z (ball_subset_closedBall hz)) EventuallyEq.rfl]
  exact hwH z hz

end CalderonN
