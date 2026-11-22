module

public import Proof.CalderonN.NormalJointEndpointJets

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalJointSecondEndpointBound.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 20
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Full second derivative control, including mixed center and velocity jets. -/
theorem Background.normal_exp_second_fderiv_bound {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : (X dim)} (hy : y ∈ Y) (hR : ContinuousAt R y) (v : (X dim))
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ expMap) (y,v)‖ ≤ backgroundSecondNormalVariationBudget dim hm K M := by
  have hC : 0 ≤ 3*(dim : ℝ)^4*K*|M ⟨1,by omega⟩| := by positivity
  have hD : 0 ≤ backgroundConnectionDerivativeBudget dim (show 2 ≤ m by omega) K M := by
    unfold backgroundConnectionDerivativeBudget
    positivity
  have hE : 0 ≤ backgroundSecondConnectionBudget dim hm K M := by
    unfold backgroundSecondConnectionBudget secondConnectionBudget
    positivity
  have hBudget : 0 ≤ backgroundSecondNormalVariationBudget dim hm K M := by
    unfold backgroundSecondNormalVariationBudget secondNormalVariationBudget
    positivity
  apply ContinuousLinearMap.opNorm_le_bound₂ _ hBudget
  intro a b
  have hConn (x : X dim) (hx : x ∈ Ω) :=
    h.1.connection_operator_bounds hΩ hK hx |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
      (abs_nonneg _) (abs_nonneg _)
      (fun i j => (h.reference_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
      (fun i j => (h.reference_second_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
  have hb := hN.joint_second_variation_bound hY hΩ h.1 hK hC hD hE
    (fun x hx => (hConn x hx).1.trans_eq (by ring))
    (fun x hx => (hConn x hx).2)
    (fun x hx => h.connection_second_derivative_budget hΩ hK hm hx) hy hR v b a hv hv1
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hh := (norm_fst_le (secondParameterVariation (normalJointPhase expMap) b a ((y,v),1))).trans hb
  rw [hN.joint_second_variation_position_eq hY hΩ h.1 hy hR v b a hv] at hh
  exact hh.trans_eq (by dsimp only [backgroundSecondNormalVariationBudget];ring)

end CalderonN
