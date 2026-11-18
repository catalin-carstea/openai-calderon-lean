import Proof.NormalJointEndpointJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 20
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Full second derivative control, including mixed center and velocity jets. -/
theorem Background.normal_exp_second_fderiv_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : X} (hy : y ∈ Y) (hR : ContinuousAt R y) (v : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ expMap) (y,v)‖ ≤ backgroundSecondNormalVariationBudget hm K M := by
  have hC : 0 ≤ 243*K*|M ⟨1,by omega⟩| := by positivity
  have hD : 0 ≤ backgroundConnectionDerivativeBudget (show 2 ≤ m by omega) K M := by
    unfold backgroundConnectionDerivativeBudget
    positivity
  have hE : 0 ≤ backgroundSecondConnectionBudget hm K M := by
    unfold backgroundSecondConnectionBudget secondConnectionBudget
    positivity
  have hBudget : 0 ≤ backgroundSecondNormalVariationBudget hm K M := by
    unfold backgroundSecondNormalVariationBudget secondNormalVariationBudget
    positivity
  apply ContinuousLinearMap.opNorm_le_bound₂ _ hBudget
  intro a b
  have hb := hN.joint_second_variation_bound hY hΩ h.1 hK hC hD hE
    (fun x hx => h.connection_budget hK (by omega) hx)
    (fun x hx => h.connection_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_second_derivative_budget hΩ hK hm hx) hy hR v b a hv hv1
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hh := (norm_fst_le (secondParameterVariation (normalJointPhase expMap) b a ((y,v),1))).trans hb
  rw [hN.joint_second_variation_position_eq hY hΩ h.1 hy hR v b a hv] at hh
  exact hh.trans_eq (by dsimp only [backgroundSecondNormalVariationBudget];ring)

end ShrinkingSpheres
