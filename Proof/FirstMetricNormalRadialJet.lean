import Proof.FirstMetricConformalFactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Conformality makes the first radial jet of the genuine first-metric normal
    pullback scalar. The reference normal metric has zero first radial jet. -/
theorem Background.firstMetric_normalPullback_first_radial_jet {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (z u v : X) :
    HasDerivAt (fun s : ℝ => normalPullbackMetricPair g₁ expMap y s z u v)
      (fderiv ℝ (firstMetricConformalFactor γ g₁) y z*metricPair γ y u v) 0 := by
  have hyΩ := hN.center_mem hy
  have hFrame := hB.2.2.2.2.2.2.2 y hyΩ
  have hCurve : HasDerivAt (fun s : ℝ => expMap (y,s • z)) z 0 := by
    have hScale := (hasDerivAt_const (0:ℝ) y).prodMk ((hasDerivAt_id (0:ℝ)).smul_const z)
    have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,0)) (y,(0:ℝ) • z) := by
      simpa only [zero_smul] using (hN.differentiableAt_zero hy).hasFDerivAt
    simpa only [Function.id_def,Function.comp_def,one_smul,hN.vertical_zero hy e hFrame] using
      hE.comp_hasDerivAt 0 hScale
  have hFD : HasFDerivAt (firstMetricConformalFactor γ g₁)
      (fderiv ℝ (firstMetricConformalFactor γ g₁) y) (expMap (y,(0:ℝ) • z)) := by
    simpa only [zero_smul,hN.exp_zero hy] using
      (((hB.firstMetricConformalFactor_smooth hK).contDiffAt (hΩ.mem_nhds hyΩ)).differentiableAt (by simp)).hasFDerivAt
  have hFactor := hFD.comp_hasDerivAt 0 hCurve
  have hNormal := hN.normalPullbackMetricPair_first_zero hΩ hB.1 hK hy hyΩ e hFrame z u v
  have hProduct := hFactor.mul hNormal
  simp only [hN.normalPullbackMetricPair_zero hy e hFrame,mul_zero,add_zero] at hProduct
  have hNear : ∀ᶠ s in 𝓝 (0:ℝ),expMap (y,s • z) ∈ Ω := by
    have hp : expMap (y,(0:ℝ) • z) ∈ Ω := by simpa only [zero_smul,hN.exp_zero hy] using hyΩ
    exact hCurve.continuousAt.eventually (hΩ.mem_nhds hp)
  have hEq : (fun s : ℝ => normalPullbackMetricPair g₁ expMap y s z u v) =ᶠ[𝓝 (0:ℝ)]
      (fun s => firstMetricConformalFactor γ g₁ (expMap (y,s • z))*normalPullbackMetricPair γ expMap y s z u v) := by
    filter_upwards [hNear] with s hs
    exact hB.firstMetricPair_eq_conformalFactor hK hs _ _
  exact hProduct.congr_of_eventuallyEq hEq

/-- In the actual gamma-orthonormal frame every off-diagonal first radial metric
    jet vanishes; the diagonal derivative is a single shared scalar witness. -/
theorem Background.framed_firstMetric_first_radial_jet {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (z : X) (i j : I) :
    HasDerivAt (fun s : ℝ => framedNormalMetric g₁ e expMap y s z i j)
      (fderiv ℝ (firstMetricConformalFactor γ g₁) y (frameVector e y z)*(if i=j then 1 else 0)) 0 := by
  have hh := hB.firstMetric_normalPullback_first_radial_jet hΩ hK hN hy
    (frameVector e y z) (e y i) (e y j)
  rw [hB.2.2.2.2.2.2.2 y (hN.center_mem hy) i j] at hh
  exact hh

end ShrinkingSpheres
