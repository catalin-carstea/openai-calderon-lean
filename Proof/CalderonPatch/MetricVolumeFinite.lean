module

public import Proof.CalderonPatch.ChartDensity
public import Proof.CalderonPatch.BoundaryMetric

import Mathlib.MeasureTheory.Measure.OpenPos

public section

noncomputable section
open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (X chartVolumeMeasure)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "J" => 𝓡∂ n

/-- A canonical metric volume is locally finite, including at the
boundary. On a sufficiently small relative coordinate ball the
smooth positive chart density is bounded. -/
theorem IsMetricVolume.isLocallyFiniteMeasure {g : SmoothMetric n M} {μ : Measure M}
    (hμ : IsMetricVolume g μ) : IsLocallyFiniteMeasure μ := by
  constructor
  intro p
  let e := extChartAt J p
  let q := e p
  let ρ (x : X n) := Real.sqrt (chartMetric g p x).det
  have hP : p ∈ e.source := mem_extChartAt_source p
  have hq : q ∈ e.target := mem_extChartAt_target p
  have hd : ContinuousOn ρ e.target :=
    CalderonN.continuousOn_metricVolumeDensity (chartMetric_smooth g p)
  have hT : MeasurableSet e.target := by
    change MeasurableSet (extChartAt J p).target
    rw [extChartAt_target]
    exact (((chartAt (EuclideanHalfSpace n) p).open_target.preimage (J).continuous_symm).measurableSet).inter
      (J).isClosed_range.measurableSet
  have hρ : ∀ᶠ x in 𝓝[e.target] q, ρ x < ρ q + 1 :=
    (hd q hq).tendsto (Iio_mem_nhds (by linarith : ρ q < ρ q + 1))
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hρ)
  let B := ball q r
  let V := e.source ∩ e ⁻¹' B
  have hS : IsOpen e.source := isOpen_extChartAt_source p
  have hV : IsOpen V := (continuousOn_extChartAt p).isOpen_inter_preimage hS isOpen_ball
  have hv : p ∈ V := ⟨hP,mem_ball_self hr⟩
  refine ⟨V,hV.mem_nhds hv,?_⟩
  have hM : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    (continuousOn_extChartAt p).aemeasurable hS.measurableSet
  have hν : ((μ.restrict e.source).map e) B = μ V := by
    rw [Measure.map_apply_of_aemeasurable hM measurableSet_ball,
      Measure.restrict_apply' hS.measurableSet,inter_comm]
  rw [← hν,hμ p,withDensity_apply _ measurableSet_ball,
    Measure.restrict_restrict measurableSet_ball]
  have hm : MeasurableSet (B ∩ e.target) := measurableSet_ball.inter hT
  have hLe : (∫⁻ x in B ∩ e.target, ENNReal.ofReal (ρ x) ∂volume) ≤
      ∫⁻ _ in B ∩ e.target, ENNReal.ofReal (ρ q + 1) ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hm] with x hx
    exact ENNReal.ofReal_le_ofReal ((hR hx.1) hx.2).le
  apply hLe.trans_lt
  rw [lintegral_const,Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top)

theorem IsMetricVolume.isFiniteMeasure [CompactSpace M] {g : SmoothMetric n M} {μ : Measure M}
    (hμ : IsMetricVolume g μ) : IsFiniteMeasure μ := by
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  infer_instance

/-- A nonempty open set in the native manifold has positive metric
volume. Its intersection with the interior contains a positive-density
Euclidean chart. -/
theorem IsMetricVolume.measure_pos_of_open_nonempty {g : SmoothMetric n M} {μ : Measure M}
    (hμ : IsMetricVolume g μ) {U : Set M} (hU : IsOpen U) (hUn : U.Nonempty) :
    0 < μ U := by
  obtain ⟨p,hp,hpU⟩ := (dense_manifoldInterior (n := n) (M := M)).exists_mem_open hU hUn
  obtain ⟨e,hPe,heU,heI,he,hes⟩ := exists_interiorChart p hp hU hpU
  let γ := coordinateMetric g e
  let ν := chartVolumeMeasure e.target γ
  have hEq : (μ.restrict e.source).map e = ν := volume_eq_coordinate g μ hμ e heI he hes
  have hT : e.target.Nonempty := ⟨e p,e.map_source hPe⟩
  have hG := coordinateMetric_smooth g e he hes
  have hρa := (CalderonN.continuousOn_metricVolumeDensity hG).aemeasurable e.open_target.measurableSet
    (μ := (volume : Measure (X n)))
  have hρnz : e.target ⊆ {x | ENNReal.ofReal (Real.sqrt (γ x).det) ≠ 0} := by
    intro x hx
    exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (hG.2 x hx).det_pos)).ne'
  have hν : 0 < ν univ := by
    apply pos_iff_ne_zero.mpr
    intro hz
    unfold ν chartVolumeMeasure at hz
    rw [withDensity_apply_eq_zero' hρa.ennreal_ofReal,inter_univ] at hz
    have ha : (volume : Measure (X n)).restrict e.target e.target ≤ 0 :=
      (measure_mono hρnz).trans_eq hz
    rw [Measure.restrict_apply e.open_target.measurableSet, inter_self] at ha
    exact (not_le_of_gt (e.open_target.measure_pos _ hT)) ha
  have hE : (μ.restrict e.source).map e univ = μ e.source := by
    rw [Measure.map_apply_of_aemeasurable (e.continuousOn.aemeasurable e.open_source.measurableSet)
      MeasurableSet.univ, preimage_univ,Measure.restrict_apply_univ]
  rw [← hEq,hE] at hν
  exact hν.trans_le (measure_mono heU)

end CalderonPatch
