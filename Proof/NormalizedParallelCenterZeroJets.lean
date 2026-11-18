import Proof.NormalizedCenterDerivative
import Proof.UniformSecondConnection
import Proof.NormalEndpointJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The normalized parallel-center map is the identity at zero normal
    velocity and its first velocity derivative vanishes. These are the
    actual geodesic/Jacobi identities, not a chosen Taylor model. -/
theorem Background.normalizedParallelCenter_zero_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (hK : 0 < K) (hm : 3 ≤ m) {E : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g E R) {y : X} (hy : y ∈ Y) (hR : ContinuousAt R y) :
    normalizedParallelCenterJacobian g E y 0 = ContinuousLinearMap.id ℝ X ∧
    fderiv ℝ (normalizedParallelCenterJacobian g E y) 0 = 0 := by
  have hCenter := hN.center_mem hy
  have hFrame := h.2.2.2.2.2.2.2 y hCenter
  have hDE := (hN.hasFDerivAt_zero hY hy e hFrame).fderiv
  have hJ : normalVerticalJacobian E y 0 = ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro a
    change fderiv ℝ E (y,0) (0,a) = a
    rw [hDE]
    simp
  have hC : normalParallelCenterJacobian g E y 0 = ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro a
    rw [normalParallelCenterJacobian_apply,hDE]
    simp [← connectionBilinear_apply]
  have hZero : normalizedParallelCenterJacobian g E y 0 = ContinuousLinearMap.id ℝ X := by
    rw [normalizedParallelCenterJacobian,hJ,hC,ContinuousLinearMap.inverse_id,ContinuousLinearMap.id_comp]
  refine ⟨hZero,?_⟩
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget (by omega : 2 ≤ m) K M
  let D2 := backgroundSecondConnectionBudget hm K M
  have hC0 : 0 ≤ C := by dsimp only [C];positivity
  have hD : 0 ≤ D := by dsimp only [D,backgroundConnectionDerivativeBudget];positivity
  have hD2 : 0 ≤ D2 := by dsimp only [D2,backgroundSecondConnectionBudget,secondConnectionBudget];positivity
  have hStrict : metricPair g y (0:X) 0 < (R y)^2 := by
    simp only [metricPair,PiLp.zero_apply,mul_zero,Finset.sum_const_zero]
    exact sq_pos_of_pos (hN.2 y hy).1
  have hInvNorm : ‖(normalVerticalJacobian E y 0).inverse‖ ≤ 2 := by
    rw [hJ,ContinuousLinearMap.inverse_id]
    exact ContinuousLinearMap.norm_id_le.trans (by norm_num)
  have hh := hN.normalizedParallelCenterJacobian_derivative_bound hY hΩ h.1 hK hC0 hD hD2
    (fun x hx => h.connection_budget hK (by omega) hx)
    (fun x hx => h.connection_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_second_derivative_budget hΩ hK hm hx)
    hy hR 0 hStrict (by simp) hInvNorm
  exact norm_le_zero_iff.mp (by simpa only [norm_zero,mul_zero] using hh)

end ShrinkingSpheres
