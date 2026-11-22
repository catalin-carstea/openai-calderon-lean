module

public import Proof.CalderonN.ProductFramedStrict

import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Changing the connection in the center variable costs one power of
the radius from the phase and one from proportional metric smallness. -/
theorem framedProductHessian_le_add_connectionError
    {γ g : (MetricField dim)} {φ : (X dim) × (X dim) → ℝ} {p : (X dim) × (X dim)} (e₁ e₂ : (I dim) → (X dim))
    (he₂ : ∀ i j, metricPair γ p.2 (e₂ i) (e₂ j) = if i = j then 1 else 0)
    {r ε K C : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) (hK : 0 < K) (hC : 0 ≤ C)
    (hell : ∀ v, K⁻¹ * ‖v‖^2 ≤ metricPair γ p.2 v v ∧
      metricPair γ p.2 v v ≤ K * ‖v‖^2)
    {n : (X dim)} (hn : ‖n‖ ≤ 2)
    (hdf : ∀ v : (X dim), fderiv ℝ φ p (0,v) = -r * ⟪n,frameCoordinatesL γ p.2 e₂ v⟫_ℝ)
    (hConn : ∀ u v : (X dim),
      ‖connection g p.2 u v - connection γ p.2 u v‖ ≤ C*(ε*r)*‖u‖*‖v‖)
    (U V : (X dim)) :
    framedProductHessian γ γ φ p e₁ e₂ U V ≤
      framedProductHessian γ g φ p e₁ e₂ U V + (2*C*K*Real.sqrt K)*ε*r^2*‖V‖^2 := by
  let u := frameVectorL e₁ U
  let v := frameVectorL e₂ V
  let d := connection g p.2 v v - connection γ p.2 v v
  have hv : ‖v‖^2 ≤ K*‖V‖^2 := by
    have h := (hell v).1
    have hm : metricPair γ p.2 v v = ‖V‖^2 := by
      rw [show v = frameVector (fun _ => e₂) p.2 V from frameVectorL_apply e₂ V p.2,
        metricPair_frameVector _ _ _ _ _ he₂,EuclideanSpace.real_norm_sq_eq]
      simp only [pow_two]
    rw [hm,inv_mul_eq_div,div_le_iff₀ hK,mul_comm (‖V‖^2) K] at h
    exact h
  have hdNorm : ‖d‖ ≤ C*(ε*r)*‖v‖^2 := by
    simpa only [pow_two,mul_assoc] using hConn v v
  let S := frameCoordinatesL γ p.2 e₂
  have hS : ‖S d‖ ≤ Real.sqrt K * ‖d‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [show S d = frameCoordinates γ p.2 e₂ d from frameCoordinatesL_apply _ _ _ _,
      norm_frameCoordinates_sq _ _ _ _ he₂,mul_pow,Real.sq_sqrt hK.le]
    exact (hell d).2
  have hBound : |fderiv ℝ φ p (0,d)| ≤ (2*C*K*Real.sqrt K)*ε*r^2*‖V‖^2 := by
    rw [hdf,abs_mul,abs_neg,abs_of_nonneg hr]
    calc
      _ ≤ r * (‖n‖ * ‖S d‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hr
      _ ≤ r * (2 * (Real.sqrt K * ‖d‖)) := by gcongr
      _ ≤ r * (2 * (Real.sqrt K * (C*(ε*r)*‖v‖^2))) := by gcongr
      _ ≤ r * (2 * (Real.sqrt K * (C*(ε*r)*(K*‖V‖^2)))) := by gcongr
      _ = _ := by ring
  have hEq :
      fderiv ℝ φ p (connection γ p.1 u u,connection g p.2 v v) =
        fderiv ℝ φ p (connection γ p.1 u u,connection γ p.2 v v) +
          fderiv ℝ φ p (0,d) := by
    rw [← map_add]
    congr 1
    change (connection γ p.1 u u,connection g p.2 v v) =
      (connection γ p.1 u u+0,connection γ p.2 v v+d)
    simp [d,add_sub_cancel]
  have hOne := (le_abs_self _).trans hBound
  unfold framedProductHessian productMetricHessian
  change fderiv ℝ (fderiv ℝ φ) p (u,v) (u,v) -
      fderiv ℝ φ p (connection γ p.1 u u,connection γ p.2 v v) ≤
    fderiv ℝ (fderiv ℝ φ) p (u,v) (u,v) -
      fderiv ℝ φ p (connection γ p.1 u u,connection g p.2 v v) + _
  rw [hEq]
  linarith only [hOne]

end CalderonN
