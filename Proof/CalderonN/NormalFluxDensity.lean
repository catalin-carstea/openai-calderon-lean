module

public import Proof.CalderonN.NormalBallHarmonic
public import Proof.CalderonN.NormalGreenFlux
public import Proof.CalderonN.FixedBallGreenPairing
public import Proof.CalderonN.TransferReproduction

import Mathlib.Tactic

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option backward.isDefEq.respectTransparency.types false

/-- The normalization from surface measure to the protected probability
measure multiplies the ordinary conormal density by the sphere area. -/
@[expose] def unitSphereArea (dim : ℕ) [NeZero dim] : ℝ := ((chartSurfaceMeasure dim) univ).toReal

theorem unitSphereArea_pos : 0 < (unitSphereArea dim) := by
  have h0 : (chartSurfaceMeasure dim) univ ≠ 0 := by
    rw [ne_eq,Measure.measure_univ_eq_zero]
    exact Measure.toSphere_ne_zero _
  exact ENNReal.toReal_pos h0 (measure_ne_top _ _)

theorem integral_unitSphereArea_mul_probability (f : ↥(standardSphere dim) → ℝ) :
    (∫ w, (unitSphereArea dim) * f w ∂(sphereProbability dim)) =
      ∫ w : ↥(sphere (0 : (X dim)) 1), f w ∂(chartSurfaceMeasure dim) := by
  let σ : Measure ↥(standardSphere dim) := (volume : Measure (X dim)).toSphere
  change (∫ w, (unitSphereArea dim) * f w ∂((σ univ)⁻¹ • σ)) = ∫ w, f w ∂σ
  have hArea : (σ univ).toReal = (unitSphereArea dim) := rfl
  rw [integral_smul_measure,integral_const_mul,ENNReal.toReal_inv,hArea,smul_eq_mul,
    ← mul_assoc,inv_mul_cancel₀ (unitSphereArea_pos (dim := dim)).ne',one_mul]

/-- Once the harmonic replacement of a kernel slice is found on the
fixed ball, the difference of conormals is its exact transfer density. -/
theorem normalSphereGreenFlux_eq_conormal_density
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X dim) → ℝ} (hr : 0 < r y) (hR : r y < ρ)
    {G : (X dim) × (X dim) → ℝ} {u b : (X dim) → ℝ}
    (hu : HarmonicOnBall g (closedBallImage γ E r y) u)
    (hb : smoothNear b (closedBall (0 : (X dim)) 1))
    (hLapB : ∀ z ∈ ball (0 : (X dim)) 1,
      laplace (pullbackMetric g (normalBallChartMap E e y (r y))) b z = 0)
    (hK : smoothNear (fun z => G (normalBallChartMap E e y (r y) z,y)) (sphere (0 : (X dim)) 1))
    (hBdy : EqOn b (fun z => G (normalBallChartMap E e y (r y) z,y)) (sphere (0 : (X dim)) 1)) :
    let F := normalBallChartMap E e y (r y)
    let G' := fun z => G (F z,y)
    let q := fun z => (unitSphereArea dim) *
      (ballConormal (pullbackMetric g F) b z-ballConormal (pullbackMetric g F) G' z)
    normalSphereGreenFlux g E e r G y u =
      ∫ w : ↥(standardSphere dim), q w * u (F w) ∂(sphereProbability dim) := by
  let F := normalBallChartMap E e y (r y)
  let G' := fun z => G (F z,y)
  let a := pullbackMetric g F
  obtain ⟨U,hU,hCU,ha,hu',hLapU⟩ := harmonicOnBall_normalBallChartMap hΩ hg hE hN hy he hr hR hu
  obtain ⟨V,hV,hCV,hb⟩ := hb
  obtain ⟨S,hS,hSS,hG'⟩ := hK
  have h := unitSphereFlux_eq_conormal_density (hU.inter hV) hS
    (show closedBall (0 : (X dim)) 1 ⊆ U ∩ V from fun z hz => ⟨hCU hz,hCV hz⟩) hSS
    ⟨fun i j => (ha.1 i j).mono inter_subset_left,fun z hz => ha.2 z hz.1⟩
    (hu'.mono inter_subset_left) (hb.mono inter_subset_right) hG' hLapU hLapB hBdy
  change normalSphereGreenFlux g E e r G y u =
    ∫ w : ↥(standardSphere dim), (unitSphereArea dim) * (ballConormal a b w-ballConormal a G' w) * u (F w) ∂(sphereProbability dim)
  have hNorm := integral_unitSphereArea_mul_probability
    (fun w : ↥(standardSphere dim) => u (F w) * (ballConormal a b w-ballConormal a G' w))
  refine h.trans (hNorm.symm.trans (integral_congr_ae ?_))
  filter_upwards with w
  ring

end CalderonN
