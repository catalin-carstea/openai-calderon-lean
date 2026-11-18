import Proof.NormalJointFourthVariationBounds
import Proof.UniformFourthConnection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def backgroundFourthNormalVariationBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  fourthNormalVariationBudget K (243*K*|M ⟨1,by omega⟩|)
    (backgroundConnectionDerivativeBudget (by omega) K M)
    (backgroundSecondConnectionBudget (by omega) K M) (backgroundThirdConnectionBudget (by omega) K M) (backgroundFourthConnectionBudget hm K M)

/-- The frozen metric budgets control every joint fourth variation of the
    admitted normal map, uniformly in center and velocity. -/
theorem Background.normal_joint_fourth_variation_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v : X) (a b c d : X × X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖fourthParameterVariation (normalJointPhase expMap) a b c d ((y,v),t)‖ ≤
      backgroundFourthNormalVariationBudget hm K M*‖a‖*‖b‖*‖c‖*‖d‖ := by
  have hC : 0 ≤ 243*K*|M ⟨1,by omega⟩| := by positivity
  have hD : 0 ≤ backgroundConnectionDerivativeBudget (by omega) K M := by
    unfold backgroundConnectionDerivativeBudget
    positivity
  have hE : 0 ≤ backgroundSecondConnectionBudget (by omega) K M := by
    unfold backgroundSecondConnectionBudget secondConnectionBudget
    positivity
  have hF : 0 ≤ backgroundThirdConnectionBudget (by omega) K M := by
    unfold backgroundThirdConnectionBudget thirdConnectionBudget
    positivity
  have hG4 : 0 ≤ backgroundFourthConnectionBudget hm K M := by
    unfold backgroundFourthConnectionBudget fourthConnectionBudget fourthChristoffelBudget fourthInverseMetricBudget
    positivity
  exact hN.joint_fourth_variation_bound hY hΩ h.1 hK hC hD hE hF hG4
    (fun x hx => h.connection_budget hK (by omega) hx)
    (fun x hx => h.connection_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_second_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_third_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_fourth_derivative_budget hΩ hK hm hx) hR hy v a b c d hv hv1 ht

end ShrinkingSpheres
