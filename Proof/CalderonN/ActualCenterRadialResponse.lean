module

public import Proof.CalderonN.ActualCenterCoefficientTaylor
public import Proof.CalderonN.FiniteLinearizedRadialMidpoint

import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

/-! The finite response to a genuine horizontal coefficient derivative
has a quadratic radial remainder at the midpoint Sobolev exponent. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_center_radial_response (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let A (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      ∀ a : X dim, ‖a‖ ≤ K → ∀ f : HarmonicFiniteCoefficients dim,
        let G := scaledCenterCoefficientDerivative d y a
        let ell := centerDensityCovariantLinear d y a
        let q := harmonicFiniteDriftVariationSmooth ell f
        ∃ b w R : SmoothData dim,
          EqOn b.1 (harmonicFiniteSmooth f).1 (standardSphere dim) ∧
          EqOn w.1 0 (standardSphere dim) ∧
          EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1) ∧
          (∀ z ∈ ball (0 : X dim) 1,
            negativeBallDivergence A w.1 z = -negativeBallDivergence G b.1 z) ∧
          (∀ z, R.1 z = fderiv ℝ w.1 z z-r*fderiv ℝ q.1 z z) ∧
          ‖smoothBoundarySobolev hn 0 (by norm_num) R‖ ≤ B*r^2*‖harmonicBoundaryFiniteL 1 f‖ := by
  obtain ⟨ηG,Q,hηG,hQ,hG⟩ := uniform_actual_center_coefficient_jet (Y:=Y) (by omega : 2 ≤ dim)
    hY hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηR,B,hηR,hB,hR⟩ := uniform_finite_linearized_radial_midpoint (Y:=Y) hn hΩ
    (by omega : 4 ≤ m) K ρ c₀ M Cj hK hρ Q Q hQ hQ
  refine ⟨min ηG (min ηR (ρ/2)),B,lt_min hηG (lt_min hηR (by positivity)),hB,?_⟩
  intro floor hf ε he hes d hd y hy
  dsimp only
  intro a ha f
  let r := d.radius y
  let G := scaledCenterCoefficientDerivative d y a
  let ell := centerDensityCovariantLinear d y a
  let R := actualCenterCoefficientRemainder d y a
  obtain ⟨hEll,hRem⟩ := hG floor hf ε he (hes.trans (min_le_left _ _)) d hd y hy a ha
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hre : r ≤ ε := (le_mul_of_one_le_right hr.le
    (one_le_pow₀ (hf.trans (hd.2.2.2.2.1.2 y hy).2.1))).trans (hd.2.2.2.2.2 y hy).2
  have hrρ : r < ρ := (hre.trans (hes.trans ((min_le_right _ _).trans (min_le_right _ _)))).trans_lt
    (half_lt_self hρ)
  let U := ball (0 : X dim) 2
  have hS : ContDiffOn ℝ ∞ G U := by
    intro z hz
    have h := (hRem z (ball_subset_closedBall hz)).1
    have hg : ContDiffAt ℝ ∞ G z := by
      have hEq : G = R+(fun z => (r*ell z) • (1 : Mat dim)) := by
        funext w
        simp only [Pi.add_apply,R,G,actualCenterCoefficientRemainder,r,ell]
        abel
      rw [hEq]
      exact h.add ((contDiffAt_const.mul ell.contDiff.contDiffAt).smul contDiffAt_const)
    exact hg.contDiffWithinAt
  obtain ⟨T,hT,_,V,hV,hBV,_,hEq⟩ := exists_contDiff_extension_near_compact
    (U:=U) isOpen_ball (isCompact_closedBall (0 : X dim) (5/4))
    (closedBall_subset_ball (by norm_num : (5/4 : ℝ) < 2)) hS
  have hIncl : closedBall (0 : X dim) 1 ⊆ V :=
    (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 5/4)).trans hBV
  have hGerm (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : T =ᶠ[𝓝 z] G := by
    filter_upwards [hV.mem_nhds (hIncl hz)] with w hw using hEq hw
  have hRow (z : X dim) (hz : z ∈ standardSphere dim) : IsRadialRow z (T z) := by
    rw [(hGerm z (sphere_subset_closedBall hz)).eq_of_nhds]
    exact isRadialRow_scaledCenterCoefficientDerivative (by omega : 2 ≤ dim) hY hΩ hd
      (zero_lt_one.trans_le hK) hy a hrρ hz
  have hRem' (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) :
      let E := T-r • (fun z => ell z • (1 : Mat dim))
      ‖E z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ E z‖ ≤ Q*r^2 := by
    let E := T-r • (fun z => ell z • (1 : Mat dim))
    have hER : E =ᶠ[𝓝 z] R := by
      filter_upwards [hGerm z hz] with w hw
      simp only [E,R,actualCenterCoefficientRemainder,Pi.sub_apply,Pi.smul_apply,
        G,hw,smul_smul,r,ell]
    change ‖E z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ E z‖ ≤ Q*r^2
    rw [hER.eq_of_nhds,hER.fderiv_eq]
    exact (hRem z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) hz)).2
  obtain ⟨b,w,S,hbT,hwT,hbH,hwH,hSe,hSn⟩ :=
    hR floor hf ε he (hes.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy
      ell T hT (hEll.trans (by linarith)) hRow hRem' f
  refine ⟨b,w,S,hbT,hwT,hbH,?_,hSe,hSn⟩
  intro z hz
  rw [← negativeBallDivergence_congr_germ (hGerm z (ball_subset_closedBall hz)) EventuallyEq.rfl]
  exact hwH z hz

end CalderonN
