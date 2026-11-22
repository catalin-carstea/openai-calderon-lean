module

public import Proof.CalderonN.NormalJointSecondEndpointBound
public import Proof.CalderonN.NormalJointFourthEndpointJet

import Mathlib.Tactic

/-! Uniform joint exponential jets, including mixed center and velocity
directions, obtained from the checked variational equations. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 24
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem Background.exists_normal_exp_joint_jet_envelope (dim : ℕ) [NeZero dim]
    {K : ℝ} {m : ℕ} (M : Fin (m+1) → ℝ) (hK : 0 < K) (hm : 5 ≤ m) :
    ∃ V ≥ (1 : ℝ), ∀ {Y Ω : Set (X dim)}, IsOpen Y → IsOpen Ω →
      ∀ {g g₁ g₂ : MetricField dim} {e : Frame dim}, Background Ω K M g g₁ g₂ e →
      ∀ {expMap : (X dim) × (X dim) → X dim} {R : X dim → ℝ},
        NormalCoordinates Y Ω g expMap R → ContinuousOn R Y →
        ∀ {y : X dim}, y ∈ Y → ∀ v : X dim, metricPair g y v v < (R y)^2 → ‖v‖ ≤ 1 →
          ∀ j, 1 ≤ j → j ≤ 4 → ‖iteratedFDeriv ℝ j expMap (y,v)‖ ≤ V := by
  let C := 3*(dim : ℝ)^4*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget dim (show 2 ≤ m by omega) K M
  let V₁ := Real.exp (1+2*C*K+D*K^2)
  let V₂ := backgroundSecondNormalVariationBudget dim (show 3 ≤ m by omega) K M
  let V₃ := backgroundThirdNormalVariationBudget dim (show 4 ≤ m by omega) K M
  let V₄ := backgroundFourthNormalVariationBudget dim hm K M
  let V := max 1 (max (max V₁ V₂) (max V₃ V₄))
  refine ⟨V,le_max_left _ _,?_⟩
  intro Y Ω hY hΩ g g₁ g₂ e h E R hN hR y hy v hv hv1 j hj hj4
  have hR' : ContinuousAt R y := (hR y hy).continuousAt (hY.mem_nhds hy)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D,backgroundConnectionDerivativeBudget]; positivity
  have hConn (x : X dim) (hx : x ∈ Ω) :=
    h.1.connection_operator_bounds hΩ hK hx |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
      (abs_nonneg _) (abs_nonneg _)
      (fun i j => (h.reference_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
      (fun i j => (h.reference_second_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
  have hFirst : ‖fderiv ℝ E (y,v)‖ ≤ V₁ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    intro w
    have hb := hN.joint_variation_bound hY hΩ h.1 hK hC hD
      (fun x hx => (hConn x hx).1.trans_eq (by dsimp only [C];ring))
      (fun x hx => (hConn x hx).2) hy hR' v w.1 w.2 hv hv1
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    have hh := (norm_fst_le (firstParameterVariation (normalJointPhase E) w ((y,v),1))).trans
      (show ‖firstParameterVariation (normalJointPhase E) w ((y,v),1)‖ ≤
        ‖w‖*Real.exp ((1+2*C*K+D*K^2)*1) by
        simpa only [firstParameterVariation,normalJointVariation,Prod.eta] using hb)
    rw [hN.joint_first_variation_position_eq hy v w hv.le,mul_one,mul_comm] at hh
    exact hh
  have hmax (i : ℝ) (hi : i ≤ max (max V₁ V₂) (max V₃ V₄)) : i ≤ V :=
    hi.trans (le_max_right _ _)
  interval_cases j
  · rw [norm_iteratedFDeriv_one]
    exact hFirst.trans (hmax _ ((le_max_left _ _).trans (le_max_left _ _)))
  · rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
    exact (h.normal_exp_second_fderiv_bound hY hΩ hK (by omega) hN hy hR' v hv hv1).trans
      (hmax _ ((le_max_right _ _).trans (le_max_left _ _)))
  · rw [← norm_iteratedFDeriv_fderiv (n:=2),← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
    exact (h.normal_exp_third_fderiv_bound hY hΩ hK (by omega) hN hR hy v hv hv1).trans
      (hmax _ ((le_max_left _ _).trans (le_max_right _ _)))
  · rw [norm_iteratedFDeriv_four_eq_nested]
    exact (h.normal_exp_fourth_fderiv_bound hY hΩ hK hm hN hR hy v hv hv1).trans
      (hmax _ ((le_max_right _ _).trans (le_max_right _ _)))

end CalderonN
