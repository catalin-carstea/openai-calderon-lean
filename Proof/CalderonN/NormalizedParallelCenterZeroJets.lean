module

public import Proof.CalderonN.NormalizedCenterDerivative
public import Proof.CalderonN.NormalEndpointJets

import Proof.CalderonN.UniformSecondConnection
import Mathlib.Tactic

/-! The constant and first normal-velocity jets of the actual normalized
parallel-center Jacobian. The dimension-three argument uses the same
normal-coordinate and Jacobi identities in arbitrary dimension. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem Background.normalizedParallelCenter_zero_jets {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField dim} {e : Frame dim} (h : Background Ω K M g g₁ g₂ e)
    (hK : 0 < K) (hm : 3 ≤ m) {E : X dim × X dim → X dim} {R : X dim → ℝ}
    (hN : NormalCoordinates Y Ω g E R) {y : X dim} (hy : y ∈ Y) (hR : ContinuousAt R y) :
    normalizedParallelCenterJacobian g E y 0 = ContinuousLinearMap.id ℝ (X dim) ∧
    fderiv ℝ (normalizedParallelCenterJacobian g E y) 0 = 0 := by
  have hFrame := h.2.2.2.2.2.2.2 y (hN.center_mem hy)
  have hDE := (hN.hasFDerivAt_zero hY hy e hFrame).fderiv
  have hJ : normalVerticalJacobian E y 0 = ContinuousLinearMap.id ℝ (X dim) := by
    apply ContinuousLinearMap.ext
    intro a
    change fderiv ℝ E (y,0) (0,a) = a
    rw [hDE]
    simp
  have hC : normalParallelCenterJacobian g E y 0 = ContinuousLinearMap.id ℝ (X dim) := by
    apply ContinuousLinearMap.ext
    intro a
    rw [normalParallelCenterJacobian_apply,hDE]
    simp [← connectionBilinear_apply]
  refine ⟨by rw [normalizedParallelCenterJacobian,hJ,hC,ContinuousLinearMap.inverse_id,ContinuousLinearMap.id_comp],?_⟩
  let C := 3*(dim:ℝ)^4*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget dim (by omega : 2 ≤ m) K M
  let B := backgroundSecondConnectionBudget dim hm K M
  have hC₀ : 0 ≤ C := by dsimp only [C]; positivity
  have hD₀ : 0 ≤ D := by dsimp only [D,backgroundConnectionDerivativeBudget]; positivity
  have hB₀ : 0 ≤ B := by dsimp only [B,backgroundSecondConnectionBudget,secondConnectionBudget]; positivity
  have hConn (x : X dim) (hx : x ∈ Ω) :=
    h.1.connection_operator_bounds hΩ hK hx |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
      (abs_nonneg _) (abs_nonneg _)
      (fun i j => (h.reference_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
      (fun i j => (h.reference_second_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
  have hΓ₀ (x : X dim) (hx : x ∈ Ω) : ‖connectionBilinear g x‖ ≤ C :=
    (hConn x hx).1.trans_eq (by dsimp only [C]; ring)
  have hΓ₁ (x : X dim) (hx : x ∈ Ω) : ‖fderiv ℝ (connectionBilinear g) x‖ ≤ D := (hConn x hx).2
  have hv : metricPair g y (0:X dim) 0 < (R y)^2 := by
    simp only [metricPair,PiLp.zero_apply,mul_zero,Finset.sum_const_zero]
    exact sq_pos_of_pos (hN.2 y hy).1
  have hInv : ‖(normalVerticalJacobian E y 0).inverse‖ ≤ 2 := by
    rw [hJ,ContinuousLinearMap.inverse_id]
    exact ContinuousLinearMap.norm_id_le.trans (by norm_num)
  have hD := hN.normalizedParallelCenterJacobian_derivative_bound hY hΩ h.1 hK hC₀ hD₀ hB₀
    hΓ₀ hΓ₁ (fun x hx => h.connection_second_derivative_budget hΩ hK hm hx) hy hR 0 hv (by simp) hInv
  exact norm_le_zero_iff.mp (by simpa only [norm_zero,mul_zero] using hD)

end CalderonN
