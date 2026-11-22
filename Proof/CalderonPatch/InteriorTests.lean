module

public import Proof.CalderonPatch.ChartDensity

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Proof.CalderonN.GreenRestriction

@[expose] public section

noncomputable section
open MeasureTheory Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X chartTest contMDiff_chartTest hasCompactSupport_chartTest tsupport_chartTest_subset
  chartVolumeMeasure)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- Interior smooth test functions can take the value one at a point
while remaining compactly supported in any prescribed open neighborhood. -/
theorem exists_compactly_supported_interior_test {p : M} (hp : p ∈ (𝓡∂ n).interior M)
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ u : M → ℝ, ContMDiff J R ∞ u ∧ HasCompactSupport u ∧
      tsupport u ⊆ U ∩ (𝓡∂ n).interior M ∧ u p = 1 := by
  obtain ⟨e, hpe, heU, heI, he, _⟩ := exists_interiorChart p hp hU hpU
  obtain ⟨r, hr, hrE⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hpe))
  let φ : ContDiffBump (e p) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hφ : tsupport (φ : X n → ℝ) ⊆ e.target := by
    rw [φ.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [φ]; linarith)).trans hrE
  refine ⟨chartTest e φ, contMDiff_chartTest e he φ.contDiff φ.hasCompactSupport hφ,
    hasCompactSupport_chartTest e φ.hasCompactSupport hφ, ?_, ?_⟩
  · apply (tsupport_chartTest_subset e φ.hasCompactSupport hφ).trans
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨heU (e.map_target (hφ hx)), heI (e.map_target (hφ hx))⟩
  · rw [chartTest, indicator_of_mem hpe]
    exact φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le)

variable [MeasurableSpace M] [BorelSpace M]

/-- The canonical Riemannian volume has no atom at an interior point.
This suffices for comparing the Green inverse laws at punctures. -/
theorem metricVolume_singleton_interior (g : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) {p : M} (hp : p ∈ (𝓡∂ n).interior M) :
    μ {p} = 0 := by
  obtain ⟨e, hpe, _, heI, he, hei⟩ := exists_interiorChart p hp isOpen_univ (mem_univ p)
  have hX : chartVolumeMeasure e.target (coordinateMetric g e) {e p} = 0 := by
    apply withDensity_absolutelyContinuous _ _
    exact measure_singleton _
  have ht := volume_eq_coordinate g μ hμ e heI he hei
  rw [← ht, Measure.map_apply_of_aemeasurable
    (e.continuousOn.aemeasurable e.open_source.measurableSet) (measurableSet_singleton _),
    Measure.restrict_apply' e.open_source.measurableSet] at hX
  have hsub : ({p} : Set M) ⊆ e ⁻¹' {e p} ∩ e.source := by
    apply singleton_subset_iff.mpr
    exact ⟨mem_singleton _, hpe⟩
  exact measure_mono_null hsub hX

end CalderonPatch
