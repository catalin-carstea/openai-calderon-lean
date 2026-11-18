import Proof.FirstMetricConformalDifferential

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

/-- The actual first-metric connection in terms of its canonical conformal
    depth and the reference connection. This uses the frozen Christoffel signs. -/
theorem Background.firstMetric_connection_eq {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (a b : X) :
    connection g₁ x a b = connection γ x a b-
      (fderiv ℝ (firstMetricConformalDepth γ g₁) x a • b+
        fderiv ℝ (firstMetricConformalDepth γ g₁) x b • a-
        metricPair γ x a b • metricGradient e (firstMetricConformalDepth γ g₁) x) := by
  let t := firstMetricConformalDepth γ g₁
  let κ := Real.exp (-2*t x)
  let V := metricGradient e t x
  let W := connection γ x a b-(fderiv ℝ t x a • b+fderiv ℝ t x b • a-metricPair γ x a b • V)
  have hκ : 0 < κ := Real.exp_pos _
  have hFrame := hB.2.2.2.2.2.2.2 x hx
  have hGrad (c : X) : metricPair γ x V c = fderiv ℝ t x c :=
    metricGradient_duality γ e t x c (hB.1.2 x hx).1 hFrame
  apply metricPair_left_ext γ e x hFrame
  intro c
  have hPair : metricPair g₁ x (connection g₁ x a b) c = κ*metricPair γ x (connection g₁ x a b) c :=
    (hB.firstMetricPair_eq_conformalFactor hK hx _ _).trans
      (congrArg (fun z => z*metricPair γ x (connection g₁ x a b) c) (hB.firstMetricConformalFactor_eq_exp_depth hK hx))
  have hKoszul1 := hB.2.1.metricKoszul hΩ hK hx a b c
  rw [hPair,hB.firstMetric_metricDifferential hΩ hK hx a b c,
    hB.firstMetric_metricDifferential hΩ hK hx b a c,
    hB.firstMetric_metricDifferential hΩ hK hx c a b] at hKoszul1
  have hKoszul0 := hB.1.metricKoszul hΩ hK hx a b c
  have hPairW : metricPair γ x W c = metricPair γ x (connection γ x a b) c-
      (fderiv ℝ t x a*metricPair γ x b c+fderiv ℝ t x b*metricPair γ x a c-
        metricPair γ x a b*fderiv ℝ t x c) := by
    dsimp [W]
    rw [← metricBilinear_apply]
    simp only [map_sub,map_add,map_smul,_root_.sub_apply,_root_.add_apply,_root_.smul_apply,
      smul_eq_mul,metricBilinear_apply,hGrad]
  have hScaled : κ*(2*metricPair γ x (connection g₁ x a b) c-2*metricPair γ x W c) = 0 := by
    rw [hPairW]
    dsimp only [κ,t] at hKoszul1 ⊢
    linear_combination hKoszul1-κ*hKoszul0
  have hZero := (mul_eq_zero.mp hScaled).resolve_left hκ.ne'
  change metricPair γ x (connection g₁ x a b) c = metricPair γ x W c
  linarith only [hZero]

end ShrinkingSpheres
