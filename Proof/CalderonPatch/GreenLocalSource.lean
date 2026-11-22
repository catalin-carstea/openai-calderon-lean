module

public import Proof.CalderonPatch.GreenChartL2
public import Proof.CalderonPatch.HarmonicRieszPoint

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold RealInnerProductSpace Topology

namespace CalderonPatch

open CalderonN (X harmonicL2Space harmonicRepresentative harmonicRepresentative_spec harmonicRiesz)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Y" => X (m+1)

variable {D : DirichletData m M}

local notation "L²" => Lp ℝ 2 D.volume

namespace GreenEvaluationChart

variable (C : GreenEvaluationChart D)

local notation "𝒜" => harmonicL2Space C.chart.open_target C.metricChart.smooth_metric

/-- Move an interior Riesz representer to the global metric L²
space with the adjoint of reading the chart. -/
@[expose] def evaluationSource (x : Y) : L² :=
  C.pushSource (harmonicRiesz C.chart.open_target C.metricChart.smooth_metric x :
    𝒜)

theorem evaluationSource_ae_zero_off_chart (x : Y) :
    (C.evaluationSource x : M → ℝ) =ᵐ[D.volume.restrict C.chart.sourceᶜ] 0 :=
  C.pushSource_ae_zero_off_chart _

/-- Local evaluation of a harmonic representative of the actual weak
inverse is its Hilbert pairing with the one fixed chart source. -/
theorem evaluationSource_pair {f : L²} {u : M → ℝ}
    (hu : ContMDiffOn J R ∞ u C.chart.source)
    (hH : EqOn (nativeLaplace D.metric u) 0 C.chart.source)
    (hAE : (D.weakInverseL2 f : M → ℝ) =ᵐ[D.volume.restrict C.chart.source] u)
    {p : M} (hp : p ∈ C.chart.source) :
    ⟪C.evaluationSource (C.chart p),D.weakInverseL2 f⟫ = u p := by
  let e := C.chart
  let v := u ∘ e.symm
  let F := C.readNative (D.weakInverseL2 f)
  have hv : CalderonN.Harmonic e.target C.metricChart.metric v := by
    refine ⟨(hu.comp C.smooth_inverse e.symm.mapsTo).contDiffOn, ?_⟩
    intro z hz
    have hn := nativeLaplace_eq_coordinate D.metric e C.source_interior C.smooth C.smooth_inverse
      hu (e.map_target hz)
    rw [e.right_inv hz, hH (e.map_target hz), Pi.zero_apply] at hn
    exact hn.symm
  let w : 𝒜 := ⟨F,(CalderonN.mem_harmonicL2Space_iff e.open_target C.metricChart.smooth_metric F).2
    ⟨v,hv,C.readNative_congr_ae hAE⟩⟩
  have hEq : EqOn (harmonicRepresentative w) v e.target := by
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure Y)) _ e.open_target
      (harmonicRepresentative_spec w).1.1.continuousOn hv.1.continuousOn
    exact (harmonicRepresentative_spec w).2.symm.trans (C.readNative_congr_ae hAE)
  rw [evaluationSource,C.pushSource_pair]
  change ⟪harmonicRiesz e.open_target C.metricChart.smooth_metric (e p),w⟫ = u p
  rw [CalderonN.harmonicRiesz_pair e.open_target C.metricChart.smooth_metric (e.map_source hp) w,
    hEq (e.map_source hp)]
  change u (e.symm (e p)) = u p
  rw [e.left_inv hp]

end GreenEvaluationChart

/-- A classical local reading of the actual inverse, when the
forcing is zero in a neighborhood of the observation point. -/
theorem exists_localInverse (h : NativeInverseRegularity D)
    {U : Set M} (hU : IsOpen U) {f : L²} (hf : (f : M → ℝ) =ᵐ[D.volume.restrict U] 0) :
    ∃ u : M → ℝ, ContMDiffOn J R ∞ u U ∧ EqOn u 0 (U ∩ (J).boundary M) ∧
      EqOn (nativeLaplace D.metric u) 0 (U ∩ (J).interior M) ∧
      (D.weakInverseL2 f : M → ℝ) =ᵐ[D.volume.restrict U] u := by
  rw [D.weakInverseL2_apply]
  exact h.local_zero_forcing U hU f hf

theorem localInverse_eqOn_inter {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {f : L²} {u v : M → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v V)
    (hA : (D.weakInverseL2 f : M → ℝ) =ᵐ[D.volume.restrict U] u)
    (hB : (D.weakInverseL2 f : M → ℝ) =ᵐ[D.volume.restrict V] v) :
    EqOn u v (U ∩ V) :=
  D.eqOn_open_of_ae_eq (hU.inter hV) (hu.mono inter_subset_left) (hv.mono inter_subset_right)
    ((hA.filter_mono (ae_mono (Measure.restrict_mono_set _ inter_subset_left))).symm.trans
      (hB.filter_mono (ae_mono (Measure.restrict_mono_set _ inter_subset_right))))

/-- Choosing distinct interior charts around the same point does not
alter the inverse pairing on forcings that vanish on both charts. -/
theorem evaluationSources_agree (h : NativeInverseRegularity D) (C E : GreenEvaluationChart D)
    {p : M} (hpC : p ∈ C.chart.source) (hpE : p ∈ E.chart.source)
    {f : L²} (hfC : (f : M → ℝ) =ᵐ[D.volume.restrict C.chart.source] 0)
    (hfE : (f : M → ℝ) =ᵐ[D.volume.restrict E.chart.source] 0) :
    ⟪D.weakInverseL2 (C.evaluationSource (C.chart p)),f⟫ =
    ⟪D.weakInverseL2 (E.evaluationSource (E.chart p)),f⟫ := by
  obtain ⟨u,hu,_,huH,huA⟩ := exists_localInverse h C.chart.open_source hfC
  obtain ⟨v,hv,_,hvH,hvA⟩ := exists_localInverse h E.chart.open_source hfE
  have huI : C.chart.source ⊆ C.chart.source ∩ (J).interior M := fun x hx =>
    ⟨hx,C.source_interior hx⟩
  have hvI : E.chart.source ⊆ E.chart.source ∩ (J).interior M := fun x hx =>
    ⟨hx,E.source_interior hx⟩
  rw [D.weakInverseL2_symmetric, D.weakInverseL2_symmetric,
    C.evaluationSource_pair hu (huH.mono huI) huA hpC,
    E.evaluationSource_pair hv (hvH.mono hvI) hvA hpE]
  exact localInverse_eqOn_inter C.chart.open_source E.chart.open_source hu.continuousOn
    hv.continuousOn huA hvA ⟨hpC,hpE⟩

omit [T2Space M] [CompactSpace M] [BorelSpace M] [PreconnectedSpace M] in
/-- Localized orthogonality identifies two L² readings. -/
theorem lp_ae_eq_of_supported_pairings {U : Set M} (hU : MeasurableSet U) (a b : L²)
    (h : ∀ f : L², (f : M → ℝ) =ᵐ[D.volume.restrict Uᶜ] 0 → ⟪a,f⟫ = ⟪b,f⟫) :
    (a : M → ℝ) =ᵐ[D.volume.restrict U] b := by
  have hf := (Lp.memLp (a-b)).indicator hU.nullMeasurableSet
  let f := hf.toLp (U.indicator ((a-b : L²) : M → ℝ))
  have hFoff : (f : M → ℝ) =ᵐ[D.volume.restrict Uᶜ] 0 := by
    filter_upwards [ae_restrict_of_ae hf.coeFn_toLp, ae_restrict_mem hU.compl (μ := D.volume)]
      with x hx hxu
    rw [hx,indicator_of_notMem (show x ∉ U from hxu)]
    rfl
  have hPair : ⟪a-b,f⟫ = 0 := by rw [inner_sub_left,h f hFoff,sub_self]
  have hFF : ⟪f,f⟫ = ⟪a-b,f⟫ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    by_cases hm : x ∈ U
    · rw [indicator_of_mem hm]
    · rw [indicator_of_notMem hm,inner_zero_left,inner_zero_right]
  have hzero : f = 0 := inner_self_eq_zero.mp (hFF.trans hPair)
  have hAE : (f : M → ℝ) =ᵐ[D.volume] 0 := hzero ▸ Lp.coeFn_zero _ _ _
  filter_upwards [ae_restrict_of_ae hAE, ae_restrict_of_ae hf.coeFn_toLp,
    ae_restrict_of_ae (Lp.coeFn_sub a b), ae_restrict_mem hU (μ := D.volume)]
    with x hx hfu hsub hxu
  rw [indicator_of_mem hxu, hsub, Pi.sub_apply, hx, Pi.zero_apply] at hfu
  exact sub_eq_zero.mp hfu.symm

end CalderonPatch
