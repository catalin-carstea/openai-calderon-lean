module

public import Proof.CalderonPatch.BoundaryMetric

import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricCalculus
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

public section
noncomputable section
open Filter Matrix MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (I X Mat axis chartVolume coordinateMatrix coordinateMatrix_apply vector_eq_sum_axis)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "E" => X n

private def tangentMetricMatrix (g : SmoothMetric n M) (p : M) : Mat n :=
  fun i j => g.inner p (axis i) (axis j)

private theorem chartMetric_eq_tangentMetricMatrix (g : SmoothMetric n M) (p : M) (y : E) :
    let e := extChartAt J p
    let A : E →L[ℝ] E := mfderivWithin K J e.symm (range J) y
    chartMetric g p y = (coordinateMatrix A)ᵀ * tangentMetricMatrix g (e.symm y) * coordinateMatrix A := by
  let e := extChartAt J p
  let A : E →L[ℝ] E := mfderivWithin K J e.symm (range J) y
  change chartMetric g p y = (coordinateMatrix A)ᵀ * tangentMetricMatrix g (e.symm y) * coordinateMatrix A
  ext i j
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (e.symm y)
  change B (A (axis i)) (A (axis j)) = _
  have ha (a b : I n) : B (A (axis a)) (A (axis b)) =
      ∑ k, ∑ l, (A (axis a)) k * ((A (axis b)) l * tangentMetricMatrix g (e.symm y) k l) := by
    conv_lhs => rw [← vector_eq_sum_axis (A (axis a)),← vector_eq_sum_axis (A (axis b))]
    simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      change (A (axis b)) l * ((A (axis a)) k * B (axis k) (axis l)) =
        (A (axis a)) k * ((A (axis b)) l * B (axis k) (axis l))
      ring
  rw [ha i j]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,coordinateMatrix_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

private def metricDensityRatio (g G : SmoothMetric n M) (x : M) : ℝ :=
  Real.sqrt (tangentMetricMatrix G x).det / Real.sqrt (tangentMetricMatrix g x).det

private theorem metricDensityRatio_in_chart (g G : SmoothMetric n M) (p : M)
    {x : M} (hx : x ∈ (extChartAt J p).source) :
    metricDensityRatio g G x =
      chartVolume (chartMetric G p) (extChartAt J p x) /
        chartVolume (chartMetric g p) (extChartAt J p x) := by
  let c := extChartAt J p
  let y := c x
  let A : E →L[ℝ] E := mfderivWithin K J c.symm (range J) y
  have hy : y ∈ c.target := c.map_source hx
  have hA : A.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm (I := J) hy
  obtain ⟨equiv, hequiv⟩ := hA
  have hDet : (coordinateMatrix A).det ≠ 0 := by
    rw [← hequiv]
    exact CalderonN.coordinateMatrix_det_ne_zero equiv
  have hRead (q : SmoothMetric n M) :
      chartVolume (chartMetric q p) y =
        |(coordinateMatrix A).det| * Real.sqrt (tangentMetricMatrix q x).det := by
    have h := chartMetric_eq_tangentMetricMatrix q p y
    change chartMetric q p y =
      (coordinateMatrix A)ᵀ * tangentMetricMatrix q (c.symm y) * coordinateMatrix A at h
    rw [show c.symm y = x from c.left_inv hx] at h
    simp only [chartVolume]
    rw [h,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
    rw [show (coordinateMatrix A).det * (tangentMetricMatrix q x).det * (coordinateMatrix A).det =
        ((coordinateMatrix A).det)^2 * (tangentMetricMatrix q x).det by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]
  change _ = chartVolume (chartMetric G p) y / chartVolume (chartMetric g p) y
  rw [hRead G,hRead g,mul_div_mul_left _ _ (abs_ne_zero.mpr hDet)]
  rfl

private theorem metricDensityRatio_continuous (g G : SmoothMetric n M) :
    Continuous (metricDensityRatio g G) := by
  rw [continuous_iff_continuousAt]
  intro p
  let c := extChartAt J p
  have he : ContinuousOn c c.source := continuousOn_extChartAt (I := J) p
  have hG := (CalderonN.contDiffOn_metric_volume (chartMetric_smooth G p)).continuousOn
  have hg := (CalderonN.contDiffOn_metric_volume (chartMetric_smooth g p)).continuousOn
  have hg0 : ∀ y ∈ c.target, chartVolume (chartMetric g p) y ≠ 0 :=
    fun y hy => (Real.sqrt_pos.mpr (chartMetric_posDef g p hy).det_pos).ne'
  have hR := (hG.div hg hg0).comp he (fun _ hq => c.map_source hq)
  have hN := (isOpen_extChartAt_source (I := J) p).mem_nhds (mem_extChartAt_source (I := J) p)
  exact (hR.continuousAt hN).congr
    (Filter.mem_of_superset hN fun x hx => (metricDensityRatio_in_chart g G p hx).symm)

omit [TopologicalSpace M] in
private theorem map_withDensity_of_density_reading {Y : Type*} [MeasurableSpace Y] [MeasurableSpace M]
    {μ : Measure M} {c : M → Y} (hc : AEMeasurable c μ)
    {ρ : M → ℝ≥0∞} (hρ : AEMeasurable ρ μ)
    {d : Y → ℝ≥0∞} (hd : AEMeasurable d (μ.map c))
    (hRead : ρ =ᵐ[μ] d ∘ c) :
    (μ.withDensity ρ).map c = (μ.map c).withDensity d := by
  ext1 s hs
  have hOne : Measurable (s.indicator (1 : Y → ℝ≥0∞)) := measurable_const.indicator hs
  have hcρ := hc.mono_ac (withDensity_absolutelyContinuous μ ρ)
  calc
    _ = ∫⁻ y, s.indicator (1 : Y → ℝ≥0∞) y ∂(μ.withDensity ρ).map c :=
      (lintegral_indicator_one hs).symm
    _ = ∫⁻ x, s.indicator (1 : Y → ℝ≥0∞) (c x) ∂μ.withDensity ρ :=
      lintegral_map' hOne.aemeasurable hcρ
    _ = ∫⁻ x, ρ x * s.indicator (1 : Y → ℝ≥0∞) (c x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul₀ hρ (hOne.comp_aemeasurable hc)
    _ = ∫⁻ x, s.indicator d (c x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hRead] with x hx
      change ρ x = d (c x) at hx
      by_cases hS : c x ∈ s <;> simp [hx,hS]
    _ = ∫⁻ y, s.indicator d y ∂μ.map c := (lintegral_map' (hd.indicator hs) hc).symm
    _ = _ := by rw [lintegral_indicator hs,withDensity_apply _ hs]

variable [MeasurableSpace M] [BorelSpace M]

/-- A new smooth metric has its canonical volume on the same
manifold, obtained by weighting a given canonical volume with the
ratio of the two positive Riemannian densities. -/
theorem exists_metricVolume_of_metricVolume (g G : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) : ∃ ν : Measure M, IsMetricVolume G ν := by
  let ρ (x : M) := ENNReal.ofReal (metricDensityRatio g G x)
  have hρ : Continuous ρ := ENNReal.continuous_ofReal.comp (metricDensityRatio_continuous g G)
  refine ⟨μ.withDensity ρ,?_⟩
  intro p
  let c := extChartAt J p
  let μChart := μ.restrict c.source
  let μE : Measure E := volume.restrict c.target
  let a (y : E) := ENNReal.ofReal (chartVolume (chartMetric g p) y)
  let b (y : E) := ENNReal.ofReal (chartVolume (chartMetric G p) y)
  let d (y : E) := ρ (c.symm y)
  have hSrc : MeasurableSet c.source := (isOpen_extChartAt_source (I := J) p).measurableSet
  have hTar : MeasurableSet c.target := by
    change MeasurableSet (extChartAt J p).target
    rw [extChartAt_target]
    exact (((chartAt (EuclideanHalfSpace n) p).open_target).preimage
      (𝓡∂ n).continuous_symm).measurableSet.inter (𝓡∂ n).isClosed_range.measurableSet
  have hC : AEMeasurable c μChart := (continuousOn_extChartAt (I := J) p).aemeasurable hSrc
  have hChart : μChart.map c = μE.withDensity a := hμ p
  have ha : AEMeasurable a μE :=
    (ENNReal.continuous_ofReal.continuousOn.comp
      (CalderonN.contDiffOn_metric_volume (chartMetric_smooth g p)).continuousOn (mapsTo_univ _ _)).aemeasurable hTar
  have hd : AEMeasurable d μE :=
    (hρ.continuousOn.comp (continuousOn_extChartAt_symm (I := J) p) (mapsTo_univ _ _)).aemeasurable hTar
  have hd' : AEMeasurable d (μChart.map c) :=
    hChart.symm ▸ hd.mono_ac (withDensity_absolutelyContinuous μE a)
  have hRead : ρ =ᵐ[μChart] d ∘ c := by
    filter_upwards [ae_restrict_mem hSrc] with x hx
    change ρ x = ρ (c.symm (c x))
    rw [c.left_inv hx]
  change ((μ.withDensity ρ).restrict c.source).map c = μE.withDensity b
  rw [restrict_withDensity hSrc,map_withDensity_of_density_reading hC hρ.measurable.aemeasurable hd' hRead,
    hChart,← withDensity_mul₀ ha hd]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hTar] with y hy
  have h := metricDensityRatio_in_chart g G p (c.map_target hy)
  change metricDensityRatio g G (c.symm y) =
    chartVolume (chartMetric G p) (c (c.symm y)) / chartVolume (chartMetric g p) (c (c.symm y)) at h
  rw [c.right_inv hy] at h
  change ENNReal.ofReal (chartVolume (chartMetric g p) y) *
    ENNReal.ofReal (metricDensityRatio g G (c.symm y)) = ENNReal.ofReal (chartVolume (chartMetric G p) y)
  have hPos : 0 < chartVolume (chartMetric g p) y :=
    Real.sqrt_pos.mpr (chartMetric_posDef g p hy).det_pos
  rw [← ENNReal.ofReal_mul hPos.le,h]
  congr 1
  field_simp [hPos.ne']

end CalderonPatch
