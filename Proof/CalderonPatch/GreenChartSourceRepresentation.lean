module

public import Proof.CalderonPatch.NativeCapGreenKernel
public import Proof.CalderonN.GreenRestriction

import Mathlib.MeasureTheory.Integral.Bochner.Set

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (X chartTest chartVolume chartVolumeMeasure InteriorMetricChart IsDirichletGreenKernel)

section ChangeOfVariables

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} {L : (M → ℝ) → M → ℝ}

/-- The inverse chart transports the chart density measure back to the
restriction of the native metric volume. -/
private theorem map_chartVolume_symm (C : InteriorMetricChart (𝓡∂ n) μ L) :
    (chartVolumeMeasure C.chart.target C.metric).map C.chart.symm = μ.restrict C.chart.source := by
  let e := C.chart
  let ν := chartVolumeMeasure e.target C.metric
  have hν : (μ.restrict e.source).map e = ν := C.volume_eq
  have he : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hInv : AEMeasurable (e.symm : X n → M) ν :=
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  change ν.map e.symm = _
  rw [← hν, AEMeasurable.map_map_of_aemeasurable (hν ▸ hInv) he]
  calc
    _ = (μ.restrict e.source).map id := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem e.open_source.measurableSet] with p hp
      exact e.left_inv hp
    _ = _ := Measure.map_id

/-- Integrating a supported chart test against a native L¹ function gives
the same integral in coordinate volume with the exact metric density. -/
theorem integral_chartTest_mul_of_tsupport (C : InteriorMetricChart (𝓡∂ n) μ L)
    {V : Set (X n)} (hV : V ⊆ C.chart.target) {f : X n → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hSup : tsupport f ⊆ V)
    {W : M → ℝ} (hW : Integrable W μ) :
    (∫ p, chartTest C.chart f p * W p ∂μ) =
      ∫ x in V, f x * W (C.chart.symm x) * chartVolume C.metric x := by
  let e := C.chart
  let ν := chartVolumeMeasure e.target C.metric
  have hν : (μ.restrict e.source).map e = ν := C.volume_eq
  let F (x : X n) := f x * W (e.symm x)
  have he : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hInv : AEMeasurable (e.symm : X n → M) ν :=
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hIntMap : Integrable W (ν.map e.symm) := by
    rw [map_chartVolume_symm C]
    exact hW.integrableOn
  obtain ⟨B,hB⟩ := hf.bounded_above_of_compact_support hc
  have hF : Integrable F ν :=
    (hIntMap.comp_aemeasurable hInv).bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hB)
  calc
    _ = ∫ p in e.source, F (e p) ∂μ := by
      rw [← integral_indicator e.open_source.measurableSet]
      apply integral_congr_ae
      filter_upwards with p
      change e.source.indicator (f ∘ e) p * W p = e.source.indicator (F ∘ e) p
      by_cases hp : p ∈ e.source
      · simp only [indicator_of_mem hp, Function.comp_apply, F, e.left_inv hp]
      · simp only [indicator_of_notMem hp,zero_mul]
    _ = ∫ x, F x ∂ν := by
      rw [← hν, integral_map he]
      exact hν ▸ hF.aestronglyMeasurable
    _ = ∫ x in e.target, F x * chartVolume C.metric x :=
      CalderonN.integral_chartVolume e.open_target C.metric C.smooth_metric F
    _ = _ := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_target.measurableSet hV
      intro x hx
      exact mul_eq_zero_of_left (mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport
        (fun hs => hx.2 (hSup hs))) _) _

end ChangeOfVariables

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "Y" => X (m+1)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)
variable (C : InteriorMetricChart (𝓡∂ (m+1)) D.volume (nativeLaplace D.metric))

/-- The native smooth source obtained by extending a compactly supported
coordinate test by zero. -/
@[expose] def chartTestSource (φ : Y → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hSupp : tsupport φ ⊆ C.chart.target) : Source :=
  ⟨chartTest C.chart φ, CalderonN.contMDiff_chartTest C.chart C.smooth hφ hc hSupp⟩

/-- The canonical solution on chart sources has the weighted Green
representation used for a cap's shared coordinate tests. -/
theorem smoothInverse_chartTestSource_eq_greenIntegral {G : M × M → ℝ}
    (hG : IsDirichletGreenKernel J D.volume (nativeLaplace D.metric) G)
    (hRep : ∀ q ∈ (J).interior M, ∀ f : Source,
      Integrable (fun p => G (p,q) * f p) D.volume ∧
      (∫ p, G (p,q) * f p ∂D.volume) = D.smoothInverse h f q)
    {V : Set Y} (hV : V ⊆ C.chart.target) {φ : Y → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hSupp : tsupport φ ⊆ V)
    {q : M} (hq : q ∈ (J).interior M) :
    D.smoothInverse h (chartTestSource C φ hφ hc (hSupp.trans hV)) q =
      ∫ x in V, φ x * G (C.chart.symm x,q) * chartVolume C.metric x := by
  rw [← (hRep q hq (chartTestSource C φ hφ hc (hSupp.trans hV))).2]
  change (∫ p, G (p,q) * chartTest C.chart φ p ∂D.volume) = _
  simp_rw [mul_comm (G (_,q)) (chartTest C.chart φ _)]
  exact integral_chartTest_mul_of_tsupport C hV hφ.continuous hc hSupp (hG.integrable q hq)

end CalderonPatch
