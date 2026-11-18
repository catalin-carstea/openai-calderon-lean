import Proof.UniformReferenceNormalMetricCenterTaylor
import Proof.ReferenceNormalMetricVerticalTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Center differentiation while velocity and both tangent slots are transported
    by the actual reference connection. -/
def normalMetricCovariantCenter (g : MetricField) (E : X × X → X) (y v a u w : X) : ℝ :=
  fderiv ℝ (jointNormalMetricPair g E u w) (y,v) (a,-connection g y a v)-
    jointNormalMetricPair g E (connection g y a u) w (y,v)-
    jointNormalMetricPair g E u (connection g y a w) (y,v)

/-- The actual covariant center derivative of the reference normal metric is
    quadratic in velocity, including transport of velocity and tangent slots. -/
theorem Background.normal_metric_covariant_center_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v a u w : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖normalMetricCovariantCenter g expMap y v a u w‖ ≤
      (1+3*(243*K*|M ⟨1,by omega⟩|))*backgroundJointNormalMetricJetBudget hm K M*
        ‖v‖^2*‖a‖*‖u‖*‖w‖ := by
  let Q := backgroundJointNormalMetricJetBudget hm K M
  let C := 243*K*|M ⟨1,by omega⟩|
  let B := jointNormalMetricPair g expMap u w
  let G := connection g y a
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hEnvelope := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hQ : 0 ≤ Q := by dsimp [Q,backgroundJointNormalMetricJetBudget];positivity
  have hG (z : X) : ‖G z‖ ≤ C*‖a‖*‖z‖ := by
    dsimp only [G]
    rw [← connectionBilinear_apply]
    exact (norm_bilinear_apply_le _ _ _).trans (by gcongr;exact h.connection_budget hK (by omega) (hN.center_mem hy))
  have hCenter := (h.reference_normal_metric_center_taylor hY hΩ hK hm hN hR hy v u w a 0 hv hv1).1
  have hVert := (h.reference_normal_metric_vertical_taylor hY hΩ hK hm hN hR hy v u w hv hv1).2 (-G v)
  have hLeft := (h.reference_normal_metric_vertical_taylor hY hΩ hK hm hN hR hy v (G u) w hv hv1).1
  have hRight := (h.reference_normal_metric_vertical_taylor hY hΩ hK hm hN hR hy v u (G w) hv hv1).1
  have hVertBound : ‖fderiv ℝ B (y,v) (0,-G v)‖ ≤ Q*C*‖v‖^2*‖a‖*‖u‖*‖w‖ := by
    rw [norm_neg] at hVert
    exact hVert.trans ((show Q*‖v‖*‖G v‖*‖u‖*‖w‖ ≤ Q*‖v‖*(C*‖a‖*‖v‖)*‖u‖*‖w‖ by
      gcongr;exact hG v).trans_eq (by ring))
  have hLeftBound : ‖jointNormalMetricPair g expMap (G u) w (y,v)-metricPair g y (G u) w‖ ≤
      Q*C*‖v‖^2*‖a‖*‖u‖*‖w‖ :=
    hLeft.trans ((show Q*‖v‖^2*‖G u‖*‖w‖ ≤ Q*‖v‖^2*(C*‖a‖*‖u‖)*‖w‖ by
      gcongr;exact hG u).trans_eq (by ring))
  have hRightBound : ‖jointNormalMetricPair g expMap u (G w) (y,v)-metricPair g y u (G w)‖ ≤
      Q*C*‖v‖^2*‖a‖*‖u‖*‖w‖ :=
    hRight.trans ((show Q*‖v‖^2*‖u‖*‖G w‖ ≤ Q*‖v‖^2*‖u‖*(C*‖a‖*‖w‖) by
      gcongr;exact hG w).trans_eq (by ring))
  have hEq : normalMetricCovariantCenter g expMap y v a u w =
      (fderiv ℝ B (y,v) (a,0)-metricDifferential g y a u w)+fderiv ℝ B (y,v) (0,-G v)-
      (jointNormalMetricPair g expMap (G u) w (y,v)-metricPair g y (G u) w)-
      (jointNormalMetricPair g expMap u (G w) (y,v)-metricPair g y u (G w)) := by
    have hCompat := connection_metric hΩ h.1 hK (hN.center_mem hy) a u w
    have hDir : (a,-G v) = ((a,0):X × X)+(0,-G v) := by simp
    dsimp only [normalMetricCovariantCenter]
    change fderiv ℝ B (y,v) (a,-G v)-_ - _ = _
    rw [hDir,map_add]
    dsimp only [G] at *
    linarith only [hCompat]
  rw [hEq]
  have hb := (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hCenter hVertBound)) hLeftBound)) hRightBound)
  exact hb.trans_eq (by dsimp only [Q,C];ring)

end ShrinkingSpheres
