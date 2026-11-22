module

public import Proof.CalderonPatch.Energy

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X axis)

variable {n : ℕ} [NeZero n]

private theorem volume_halfSpace_face :
    (volume : Measure (X n)) {x | x 0 = 0} = 0 := by
  let A := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).toLinearMap.ker
  have hA : A ≠ ⊤ := by
    intro h
    have hx : axis (0 : Fin n) ∈ A := h.symm ▸ Submodule.mem_top
    have he : axis (0 : Fin n) 0 = 0 := hx
    simp [axis] at he
  exact Measure.addHaar_submodule volume A hA

variable {M : Type*} [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "J" => 𝓡∂ n

private theorem metricVolume_boundary_inter_chart (g : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) (p : M) :
    μ ((𝓡∂ n).boundary M ∩ (extChartAt J p).source) = 0 := by
  let c := extChartAt J p
  let H : Set (X n) := {x | x 0 = 0}
  have hH : MeasurableSet H :=
    (isClosed_eq (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).continuous continuous_const).measurableSet
  have hs := (isOpen_extChartAt_source (I := J) p).measurableSet
  have hMc : AEMeasurable (c : M → X n) (μ.restrict c.source) :=
    (continuousOn_extChartAt (I := J) p).aemeasurable hs
  have hNull : ((μ.restrict c.source).map c) H = 0 := by
    rw [hμ p]
    exact withDensity_absolutelyContinuous _ _ (Measure.restrict_apply hH ▸
      measure_mono_null inter_subset_left volume_halfSpace_face)
  rw [Measure.map_apply_of_aemeasurable hMc hH, Measure.restrict_apply' hs] at hNull
  apply measure_mono_null _ hNull
  intro q hq
  refine ⟨?_, hq.2⟩
  have hxt := c.map_source hq.2
  have hr := extChartAt_target_subset_range (I := J) p hxt
  have hqS : q ∈ (chartAt (EuclideanHalfSpace n) p).source := by
    simpa only [extChartAt_source] using hq.2
  have hn : c q ∉ interior c.target := by
    intro ht
    have hi := ((𝓡∂ n).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas _ p) hqS).2 ht
    exact (((𝓡∂ n).isInteriorPoint_iff_not_isBoundaryPoint q).mp hi) hq.1
  have hnR : c q ∉ interior (range J) := fun h =>
    hn ((extChartAt_target_eventuallyEqSet_of_mem hxt).symm.mem_interior h)
  have hRange : range (J : EuclideanHalfSpace n → X n) = {y | 0 ≤ y 0} :=
    range_euclideanHalfSpace n
  rw [hRange] at hr
  rw [hRange, interior_halfSpace] at hnR
  exact le_antisymm (le_of_not_gt hnR) hr

/-- The frozen Riemannian density gives the boundary zero volume,
without any orientability assumption. -/
theorem metricVolume_boundary_eq_zero (g : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) : μ ((𝓡∂ n).boundary M) = 0 := by
  let U (p : M) := (extChartAt J p).source
  have hU : (univ : Set M) ⊆ ⋃ p, U p :=
    fun p _ => mem_iUnion.mpr ⟨p, mem_extChartAt_source p⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U (isOpen_extChartAt_source (I := J)) hU
  have hNull : μ (⋃ p ∈ (s : Set M), (𝓡∂ n).boundary M ∩ U p) = 0 :=
    (measure_biUnion_null_iff s.finite_toSet.countable).mpr
      (fun p _ => metricVolume_boundary_inter_chart g μ hμ p)
  apply measure_mono_null _ hNull
  intro p hp
  have hpU := hs (mem_univ p)
  simp only [mem_iUnion] at hpU ⊢
  obtain ⟨q, hq, hpq⟩ := hpU
  exact ⟨q, hq, hp, hpq⟩

end CalderonPatch
