import Proof.NormalHarmonicPullback
import Proof.Archive.FiniteDimensionalLocalSmoothExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.ConnectionError

lemma NormalCoordinates.smoothNear_normalChart_comp {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R y) (u : X → ℝ)
    (hu : smoothNear u (closedBallImage γ expMap (fun _ => r) y)) :
    smoothNear (u ∘ normalChart expMap e y r) (Metric.closedBall (0:X) 1) := by
  obtain ⟨S,hS,hIn,hF⟩ := hN.smoothNear_normalChart hy e hFrame r hr hrR
  obtain ⟨T,hT,hBall,hU⟩ := hu
  have hPhysical (z : X) (hz : z ∈ Metric.closedBall (0:X) 1) :
      normalChart expMap e y r z ∈ closedBallImage γ expMap (fun _ => r) y :=
    ⟨r • frameVector e y z,normalChart_velocity_mem γ e y hFrame r r hr.le le_rfl hz,rfl⟩
  refine ⟨S ∩ normalChart expMap e y r ⁻¹' T,
    hF.continuousOn.isOpen_inter_preimage hS hT,fun z hz => ⟨hIn hz,hBall (hPhysical z hz)⟩,?_⟩
  exact hU.comp (hF.mono inter_subset_left) (fun z hz => hz.2)

/-- A global smooth representative agreeing with the actual physical pullback
    near every point of the closed ball. No norm bound is asserted for this extension. -/
theorem NormalCoordinates.exists_global_pullback_representative {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R y) (u : X → ℝ)
    (hu : smoothNear u (closedBallImage γ expMap (fun _ => r) y)) :
    ∃ U : SmoothData,HasCompactSupport U.1 ∧ ∀ z ∈ Metric.closedBall (0:X) 1,
      U.1 =ᶠ[𝓝 z] (u ∘ normalChart expMap e y r) := by
  obtain ⟨S,hS,hIn,hSmooth⟩ := hN.smoothNear_normalChart_comp hy e hFrame r hr hrR u hu
  obtain ⟨U,hU,hComp,hNear⟩ := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.closedBall (0:X) 1) S (isCompact_closedBall _ _) hS hIn
    (u ∘ normalChart expMap e y r) hSmooth
  exact ⟨⟨U,hU⟩,hComp,hNear⟩

/-- The actual physical harmonic pullback has a genuine smooth Sobolev
    representative satisfying the same actual divergence equation. -/
theorem uniform_normal_harmonic_representative {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ u : X → ℝ,
      HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∃ U : SmoothData,HasCompactSupport U.1 ∧
        (∀ z ∈ Metric.closedBall (0:X) 1,U.1 =ᶠ[𝓝 z] (u ∘ normalChart d.expMap d.frame y (d.radius y))) ∧
        ∀ z ∈ Metric.ball (0:X) 1,coordinateFluxDivergence
          (metricDivergenceFlux (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) U.1) z = 0 := by
  obtain ⟨η,hη,hPull⟩ := uniform_normal_harmonic_pullback (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy u hu
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  obtain ⟨U,hComp,hNear⟩ := hd.2.1.exists_global_pullback_representative hy d.frame hFrame (d.radius y) hr
    (le_max_right ρ (d.radius y)) u hu.1
  refine ⟨U,hComp,hNear,?_⟩
  intro z hz
  have hFlux := metricDivergenceFlux_congr_germ
    (g:=framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
    (h:=framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
    Filter.EventuallyEq.rfl (hNear z (Metric.ball_subset_closedBall hz))
  exact (coordinateFluxDivergence_congr_germ hFlux).trans
    (hPull floor hf ε hε hSmall d hd y hy u hu z hz)

end ShrinkingSpheres
