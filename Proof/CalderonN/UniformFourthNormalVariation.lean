module

public import Proof.CalderonN.NormalJointFourthVariationBounds
public import Proof.CalderonN.UniformFourthConnection

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/UniformFourthNormalVariation.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def backgroundFourthNormalVariationBudget (dim : ℕ) {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  fourthNormalVariationBudget K (3*(dim : ℝ)^4*K*|M ⟨1,by omega⟩|)
    (backgroundConnectionDerivativeBudget dim (by omega) K M)
    (backgroundSecondConnectionBudget dim (by omega) K M) (backgroundThirdConnectionBudget dim (by omega) K M) (backgroundFourthConnectionBudget dim hm K M)

/-- The frozen metric budgets control every joint fourth variation of the
    admitted normal map, uniformly in center and velocity. -/
theorem Background.normal_joint_fourth_variation_bound {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (a b c d : (X dim) × (X dim))
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖fourthParameterVariation (normalJointPhase expMap) a b c d ((y,v),t)‖ ≤
      backgroundFourthNormalVariationBudget dim hm K M*‖a‖*‖b‖*‖c‖*‖d‖ := by
  have hC : 0 ≤ 3*(dim : ℝ)^4*K*|M ⟨1,by omega⟩| := by positivity
  have hD : 0 ≤ backgroundConnectionDerivativeBudget dim (by omega) K M := by
    unfold backgroundConnectionDerivativeBudget
    positivity
  have hE : 0 ≤ backgroundSecondConnectionBudget dim (by omega) K M := by
    unfold backgroundSecondConnectionBudget secondConnectionBudget
    positivity
  have hF : 0 ≤ backgroundThirdConnectionBudget dim (by omega) K M := by
    unfold backgroundThirdConnectionBudget thirdConnectionBudget
    positivity
  have hG4 : 0 ≤ backgroundFourthConnectionBudget dim hm K M := by
    unfold backgroundFourthConnectionBudget fourthConnectionBudget fourthChristoffelBudget fourthInverseMetricBudget
    positivity
  have hConn (x : X dim) (hx : x ∈ Ω) :=
    h.1.connection_operator_bounds hΩ hK hx |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
      (abs_nonneg _) (abs_nonneg _)
      (fun i j => (h.reference_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
      (fun i j => (h.reference_second_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
  exact hN.joint_fourth_variation_bound hY hΩ h.1 hK hC hD hE hF hG4
    (fun x hx => (hConn x hx).1.trans_eq (by ring))
    (fun x hx => (hConn x hx).2)
    (fun x hx => h.connection_second_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_third_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_fourth_derivative_budget hΩ hK hm hx) hR hy v a b c d hv hv1 ht

end CalderonN
