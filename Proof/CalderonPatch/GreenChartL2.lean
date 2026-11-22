module

public import Proof.CalderonPatch.GreenInversePairing
public import Proof.CalderonN.HarmonicJetEvaluation

import Proof.CalderonPatch.ChartDensity
import Proof.CalderonPatch.ChartEnergyIntegral
import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold RealInnerProductSpace Topology

namespace CalderonPatch

open CalderonN (X I chartVolumeMeasure chartVolume InteriorMetricChart ChartL2)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Y" => X (m+1)
local notation "K" => 𝓘(ℝ, Y)

/-- An interior chart for local evaluation, with the canonical volume
bounded below by a positive multiple of Lebesgue measure. -/
structure GreenEvaluationChart (D : DirichletData m M) where
  chart : OpenPartialHomeomorph M Y
  source_interior : chart.source ⊆ (J).interior M
  smooth : ContMDiffOn J K ∞ chart chart.source
  smooth_inverse : ContMDiffOn K J ∞ chart.symm chart.target
  scale : ℝ≥0∞
  scale_finite : scale ≠ ⊤
  measure_le : (volume : Measure Y).restrict chart.target ≤ scale •
    chartVolumeMeasure chart.target (coordinateMetric D.metric chart)

namespace GreenEvaluationChart

variable {D : DirichletData m M} (C : GreenEvaluationChart D)

@[expose] def metricChart : InteriorMetricChart J D.volume (nativeLaplace D.metric) :=
  nativeInteriorMetricChart D.metric D.volume D.metric_volume C.chart
    C.source_interior C.smooth C.smooth_inverse

local notation "ν" => chartVolumeMeasure C.chart.target C.metricChart.metric
local notation "λ₀" => Measure.restrict (volume : Measure Y) C.chart.target

omit [CompactSpace M] [PreconnectedSpace M] in
theorem exists_chart_at (D : DirichletData m M)
    {p : M} (hp : p ∈ (J).interior M) {W : Set M} (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ C : GreenEvaluationChart D, p ∈ C.chart.source ∧ closure C.chart.source ⊆ W := by
  obtain ⟨a,hpa,haW,haI,ha,has⟩ := exists_interiorChart p hp hW hpW
  let A := nativeInteriorMetricChart D.metric D.volume D.metric_volume a haI ha has
  obtain ⟨r,hr,hrA⟩ := Metric.mem_nhds_iff.mp (a.open_target.mem_nhds (a.map_source hpa))
  let B := Metric.ball (a p) (r/2)
  let C₀ := Metric.closedBall (a p) (r/2)
  have hC : C₀ ⊆ a.target := (Metric.closedBall_subset_ball (by linarith)).trans hrA
  have hB : B ⊆ a.target := Metric.ball_subset_closedBall.trans hC
  obtain ⟨A',hS,hT,hInv,hMetric⟩ := restrict_interiorMetricChart A Metric.isOpen_ball hB
  have hAS : p ∈ A'.chart.source := by
    rw [hS]
    exact ⟨hpa,Metric.mem_ball_self (by positivity)⟩
  have hPos : ∀ z ∈ C₀, 0 < chartVolume A.metric z := fun z hz =>
    Real.sqrt_pos.mpr (A.smooth_metric.2 z (hC hz)).det_pos
  obtain ⟨z,hz,hMin⟩ := (isCompact_closedBall (a p) (r/2)).exists_isMinOn
    ⟨a p,Metric.mem_closedBall_self (by positivity)⟩
    ((CalderonN.continuousOn_metricVolumeDensity A.smooth_metric).mono hC)
  let δ := ENNReal.ofReal (chartVolume A.metric z)
  have hδ₀ : δ ≠ 0 := (ENNReal.ofReal_pos.mpr (hPos z hz)).ne'
  have hδfin : δ ≠ ⊤ := ENNReal.ofReal_ne_top
  let C' : GreenEvaluationChart D :=
    { chart := A'.chart
      source_interior := A'.source_interior
      smooth := A'.smooth
      smooth_inverse := A'.smooth_inverse
      scale := δ⁻¹
      scale_finite := ENNReal.inv_ne_top.mpr hδ₀
      measure_le := by
        let v := (volume : Measure Y).restrict A'.chart.target
        have hd : δ • v ≤ chartVolumeMeasure A'.chart.target (coordinateMetric D.metric A'.chart) := by
          rw [← withDensity_const]
          apply withDensity_mono
          filter_upwards [ae_restrict_mem A'.chart.open_target.measurableSet] with x hx
          have hxB : x ∈ B := by rwa [hT] at hx
          have hEq : coordinateMetric D.metric A'.chart x = A.metric x := by
            change (fun i j => D.metric.inner (A'.chart.symm x)
              (mfderiv K J A'.chart.symm x (CalderonN.axis i))
              (mfderiv K J A'.chart.symm x (CalderonN.axis j))) = A.metric x
            rw [hInv]
            rfl
          exact ENNReal.ofReal_le_ofReal (by
            change chartVolume A.metric z ≤ chartVolume (coordinateMetric D.metric A'.chart) x
            rw [show chartVolume (coordinateMetric D.metric A'.chart) x = chartVolume A.metric x from
              congrArg (fun a : CalderonN.Mat (m+1) => Real.sqrt a.det) hEq]
            exact hMin (Metric.ball_subset_closedBall hxB))
        calc
          _ = δ⁻¹ • (δ • v) := by rw [smul_smul, ENNReal.inv_mul_cancel hδ₀ hδfin,one_smul]
          _ ≤ _ := by
            apply Measure.le_iff.mpr
            intro s hs
            exact mul_le_mul_of_nonneg_left (Measure.le_iff'.mp hd s) zero_le }
  refine ⟨C',hAS,?_⟩
  have hImg : A'.chart.source ⊆ a.symm '' C₀ := by
    intro x hx
    have hx' := (show x ∈ a.source ∩ a ⁻¹' B from hS ▸ hx)
    exact ⟨a x,Metric.ball_subset_closedBall hx'.2,a.left_inv hx'.1⟩
  exact (closure_minimal hImg ((isCompact_closedBall (a p) (r/2)).image_of_continuousOn
    (a.continuousOn_symm.mono hC)).isClosed).trans
    (image_subset_iff.mpr (fun z hz => haW (a.map_target (hC hz))))

omit [T2Space M] [CompactSpace M] [PreconnectedSpace M] in
private theorem target_ae_metric (C : GreenEvaluationChart D) :
    ∀ᵐ x ∂chartVolumeMeasure C.chart.target C.metricChart.metric, x ∈ C.chart.target :=
  (ae_restrict_mem C.chart.open_target.measurableSet).filter_mono
    ((withDensity_absolutelyContinuous _ _).ae_le)

private noncomputable def measurableInverse (C : GreenEvaluationChart D) : Y → M := by
  classical
  exact C.chart.target.piecewise C.chart.symm (fun _ => C.chart.symm 0)

omit [T2Space M] [CompactSpace M] [PreconnectedSpace M] in
private theorem measurable_measurableInverse : Measurable C.measurableInverse := by
  classical
  unfold measurableInverse
  exact C.chart.continuousOn_symm.measurable_piecewise
    continuousOn_const C.chart.open_target.measurableSet

omit [T2Space M] [CompactSpace M] [PreconnectedSpace M] in
private theorem measurableInverse_ae : C.measurableInverse =ᵐ[ν] C.chart.symm := by
  classical
  exact (target_ae_metric C).mono (fun z hz => piecewise_eq_of_mem _ _ _ hz)

omit [T2Space M] [CompactSpace M] [PreconnectedSpace M] in
private theorem measurableInverse_preserves :
    MeasurePreserving C.measurableInverse ν (D.volume.restrict C.chart.source) := by
  classical
  refine ⟨C.measurable_measurableInverse,?_⟩
  have hν : (D.volume.restrict C.chart.source).map C.chart = ν := C.metricChart.volume_eq
  have hF : AEMeasurable (C.chart : M → Y) (D.volume.restrict C.chart.source) :=
    C.chart.continuousOn.aemeasurable C.chart.open_source.measurableSet
  rw [← hν, AEMeasurable.map_map_of_aemeasurable C.measurable_measurableInverse.aemeasurable hF]
  have heq : C.measurableInverse ∘ C.chart =ᵐ[D.volume.restrict C.chart.source] id := by
    filter_upwards [ae_restrict_mem C.chart.open_source.measurableSet (μ := D.volume)] with p hp
    change C.measurableInverse (C.chart p) = p
    rw [measurableInverse,piecewise_eq_of_mem _ _ _ (C.chart.map_source hp), C.chart.left_inv hp]
  rw [Measure.map_congr heq, Measure.map_id]

omit [T2Space M] [CompactSpace M] [PreconnectedSpace M] in
private theorem chart_ac : λ₀ ≪ ν :=
  (Measure.absolutelyContinuous_of_le_smul C.measure_le)

local notation "L²ₘ" => Lp ℝ 2 (D.volume.restrict C.chart.source)
local notation "L²ₑ" => ChartL2 (d := m+1) (C.chart.target)
local notation "L²" => Lp ℝ 2 D.volume

/-- Pull back the actual restricted metric L² class to a local
Lebesgue L² class, using the lower metric density bound. -/
def localReading : L²ₘ →L[ℝ] L²ₑ :=
  (Lp.LpToLpOfMeasureLeSMul C.scale_finite C.measure_le).comp
    (Lp.compMeasurePreservingₗᵢ ℝ C.measurableInverse C.measurableInverse_preserves).toContinuousLinearMap

omit [T2Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem localReading_ae (f : L²ₘ) :
    (C.localReading f : Y → ℝ) =ᵐ[λ₀] (f : M → ℝ) ∘ C.chart.symm := by
  unfold localReading
  refine (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).trans ?_
  exact ((Lp.coeFn_compMeasurePreserving f C.measurableInverse_preserves).trans
    (C.measurableInverse_ae.mono fun z h => congrArg (f : M → ℝ) h)).filter_mono
      C.chart_ac.ae_le

theorem localReading_congr_ae {f : L²ₘ} {u : M → ℝ}
    (h : (f : M → ℝ) =ᵐ[D.volume.restrict C.chart.source] u) :
    (C.localReading f : Y → ℝ) =ᵐ[λ₀] u ∘ C.chart.symm := by
  refine (C.localReading_ae f).trans ?_
  have hMap : (f : M → ℝ) =ᵐ[Measure.map C.measurableInverse ν] u := by
    rw [C.measurableInverse_preserves.map_eq]
    exact h
  have h' := ae_of_ae_map C.measurable_measurableInverse.aemeasurable hMap
  apply C.chart_ac.ae_eq
  filter_upwards [C.measurableInverse_ae,h'] with z hz hh
  change f (C.chart.symm z) = u (C.chart.symm z)
  rw [← hz]
  exact hh

private def nativeRestriction : L² →L[ℝ] L²ₘ :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using Measure.restrict_le_self)

def readNative : L² →L[ℝ] L²ₑ :=
  C.localReading.comp C.nativeRestriction

theorem readNative_congr_ae {f : L²} {u : M → ℝ}
    (h : (f : M → ℝ) =ᵐ[D.volume.restrict C.chart.source] u) :
    (C.readNative f : Y → ℝ) =ᵐ[λ₀] u ∘ C.chart.symm := by
  unfold readNative nativeRestriction
  exact C.localReading_congr_ae ((Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).trans h)

/-- The adjoint of the chart reading uses true metric volume on the
whole manifold. Its values vanish off the chart almost everywhere. -/
def pushSource : L²ₑ →L[ℝ] L² := C.readNative.adjoint

omit [T2Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem pushSource_pair (r : L²ₑ) (f : L²) :
    ⟪C.pushSource r,f⟫ = ⟪r,C.readNative f⟫ :=
  by unfold pushSource; exact C.readNative.adjoint_inner_left f r

theorem pushSource_ae_zero_off_chart (r : L²ₑ) :
    (C.pushSource r : M → ℝ) =ᵐ[D.volume.restrict C.chart.sourceᶜ] 0 := by
  let v := C.pushSource r
  have hInd : MemLp (C.chart.sourceᶜ.indicator (v : M → ℝ)) 2 D.volume :=
    (Lp.memLp v).indicator C.chart.open_source.measurableSet.compl.nullMeasurableSet
  let w := hInd.toLp _
  have hw : (w : M → ℝ) =ᵐ[D.volume.restrict C.chart.source] 0 := by
    filter_upwards [ae_restrict_mem C.chart.open_source.measurableSet (μ := D.volume),
      ae_restrict_of_ae hInd.coeFn_toLp] with x hx hw
    rw [hw,indicator_of_notMem (show x ∉ C.chart.sourceᶜ from not_not_intro hx)]
    rfl
  have hR : C.readNative w = 0 := by
    apply Lp.ext
    exact (C.readNative_congr_ae hw).trans (Lp.coeFn_zero _ _ _).symm
  have hPair : ⟪v,w⟫ = 0 := by rw [show v = C.pushSource r from rfl, C.pushSource_pair, hR, inner_zero_right]
  have hW : ⟪w,w⟫ = ⟪v,w⟫ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hInd.coeFn_toLp] with x hx
    rw [hx]
    by_cases hm : x ∈ C.chart.sourceᶜ
    · rw [indicator_of_mem hm]
    · rw [indicator_of_notMem hm, inner_zero_left, inner_zero_right]
  have hzero : w = 0 := inner_self_eq_zero.mp (hW.trans hPair)
  have hAE : (w : M → ℝ) =ᵐ[D.volume] 0 := hzero ▸ Lp.coeFn_zero _ _ _
  filter_upwards [ae_restrict_of_ae hAE, ae_restrict_of_ae hInd.coeFn_toLp,
    ae_restrict_mem C.chart.open_source.measurableSet.compl (μ := D.volume)] with x hw hx hxC
  rw [indicator_of_mem hxC] at hx
  exact hx.symm.trans hw

end GreenEvaluationChart

end CalderonPatch
