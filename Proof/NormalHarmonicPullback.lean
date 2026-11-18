import Proof.NormalChartPullbackMetric
import Proof.MetricRadiusScaling

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

/-- The admitted physical harmonic equation pulls back to the actual normalized
    fixed-ball divergence coefficient, uniformly over every admitted radius profile. -/
theorem uniform_normal_harmonic_pullback {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ u : X → ℝ,
      HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∀ z ∈ Metric.ball (0:X) 1,
      coordinateFluxDivergence
        (metricDivergenceFlux (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
          (u ∘ normalChart d.expMap d.frame y (d.radius y))) z = 0 := by
  obtain ⟨η,hη,hE⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy u hu z hz
  let r := d.radius y
  let F := normalChart d.expMap d.frame y r
  let H := framedNormalMetric d.g₁ d.frame d.expMap y r
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hrR : r ≤ max ρ (d.radius y) := le_max_right _ _
  have hzClosed : z ∈ Metric.closedBall (0:X) 1 := Metric.ball_subset_closedBall hz
  have hVelocity := normalChart_velocity_mem d.γ d.frame y hFrame r (max ρ (d.radius y)) hr.le hrR hzClosed
  have hInterior : F z ∈ interior (closedBallImage d.γ d.expMap d.radius y) :=
    hd.2.1.normalChart_mem_interior hy d.frame hFrame r hr hrR hz
  obtain ⟨S,hS,hIn,hF⟩ := hd.2.1.smoothNear_normalChart hy d.frame hFrame r hr hrR
  obtain ⟨T,hT,hBall,hU⟩ := hu.1
  have hFzΩ : F z ∈ Ω := ((hd.2.1.2 y hy).2.2 (r • frameVector d.frame y z) hVelocity).1
  have hFzT : F z ∈ T := hBall (interior_subset hInterior)
  have hJac := hd.2.1.normalChart_jacobian_isUnit hy d.frame hFrame r hr z hVelocity
  have hPull := hd.1.2.1.pullback_flux_divergence_local hΩ hKpos F u S T hS hT hF hU z
    (hIn hzClosed) hFzT hFzΩ hJac
  have hD2 : DifferentiableAt ℝ (fderiv ℝ u) (F z) :=
    ((hU.contDiffAt (hT.mem_nhds hFzT)).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hPhysical := hd.1.2.1.flux_divergence_eq_density_laplace hΩ hKpos u hFzΩ hD2
  have hPhysicalZero : coordinateFluxDivergence (metricDivergenceFlux d.g₁ u) (F z) = 0 :=
    hPhysical.trans (by rw [hu.2 _ hInterior,mul_zero])
  have hPullZero : coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric d.g₁ F) (u ∘ F)) z = 0 :=
    hPull.trans (by rw [hPhysicalZero,mul_zero])
  have hMetricGerm : pullbackMetric d.g₁ F =ᶠ[𝓝 z] (fun w => r^2 • H w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact hd.2.1.normalChart_pullbackMetric hy d.g₁ d.frame r w
      (normalChart_velocity_mem d.γ d.frame y hFrame r (max ρ (d.radius y)) hr.le hrR (Metric.ball_subset_closedBall hw))
  have hSame := coordinateFluxDivergence_congr_germ
    (metricDivergenceFlux_congr_germ (u:=u ∘ F) (v:=u ∘ F) hMetricGerm Filter.EventuallyEq.rfl)
  have hScaledZero : coordinateFluxDivergence (metricDivergenceFlux (fun w => r^2 • H w) (u ∘ F)) z = 0 :=
    hSame.symm.trans hPullZero
  have hEll : Elliptic (Metric.closedBall (0:X) 2) (4*K^2) H :=
    hE floor hf ε hε hSmall d hd y hy d.g₁ (by simp)
  have h12 : Metric.ball (0:X) 1 ⊆ Metric.closedBall (0:X) 2 := by
    intro w hw
    change dist w 0 ≤ 2
    change dist w 0 < 1 at hw
    exact hw.le.trans (by norm_num)
  have hEllOpen : Elliptic (Metric.ball (0:X) 1) (4*K^2) H :=
    ⟨fun i j => (hEll.1 i j).mono h12,fun w hw => hEll.2 w (h12 hw)⟩
  have hScale := hEllOpen.flux_divergence_radius_sq Metric.isOpen_ball
    (show 0 < 4*K^2 by positivity) (u ∘ F) r hr hz
  have hZero : r*coordinateFluxDivergence (metricDivergenceFlux H (u ∘ F)) z = 0 :=
    hScale.symm.trans hScaledZero
  exact (mul_eq_zero.mp hZero).resolve_left hr.ne'

end ShrinkingSpheres
