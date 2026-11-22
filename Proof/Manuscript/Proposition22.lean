module

public import Proof.CalderonPatch.NativeCapAgreement
public import Proof.CalderonPatch.NativeCapGreenKernel

import Proof.CalderonPatch.CapGreenAgreement
import Proof.CalderonPatch.MetricVolumeChange
import Mathlib.Tactic

public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Manifold Topology
open CalderonN (X chartVolume IsDirichletGreenKernel)
open CalderonPatch

namespace CalderonPaper

local notation "J[" m "]" => 𝓡∂ (m+1)
local notation "Source[" m "," M "]" => smoothSourceSubmodule (m := m) (M := M)
local notation "inverse[" D "]" => DirichletData.smoothInverse D (nativeInverseRegularity D)

/-- The measured trace support controls the closure of the interior part of an
original copy's embedded boundary. -/
private theorem attachment_closure_subset {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanHalfSpace (n+1)) M]
    [IsManifold (𝓡∂ (n+1)) ∞ M] [MeasurableSpace M]
    {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}
    (C : MeasuredCommonCap d₁ d₂ Γ) :
    closure {p : (𝓡∂ (n+1)).boundary M | C.secondCopy.embed p ∈ (𝓡∂ (n+1)).interior M} ⊆ Γ := by
  let J := 𝓡∂ (n+1)
  let w : M → ℝ := ((J).interior M).indicator (fun _ => 1)
  have hTrace : EqOn w 0 ((J).boundary M) := by
    intro x hx
    have hx' : x ∈ ((J).interior M)ᶜ := by rwa [(J).compl_interior]
    exact indicator_of_notMem hx' _
  have hSup :
      Function.support (fun p : (J).boundary M => w (C.secondCopy.embed p)) =
        {p : (J).boundary M | C.secondCopy.embed p ∈ (J).interior M} := by
    ext p
    change w (C.secondCopy.embed p) ≠ 0 ↔ C.secondCopy.embed p ∈ (J).interior M
    by_cases hp : C.secondCopy.embed p ∈ (J).interior M
    · simp [w, hp]
    · simp [w, hp]
  have h := (C.traces_supported w hTrace).2
  change closure (Function.support _) ⊆ Γ at h
  rwa [hSup] at h

/-- The bump is positive at its center, so the second original center lies
in the extended interior. -/
private theorem attachment_center {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
    [MeasurableSpace M]
    {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}
    (C : MeasuredCommonCap d₁ d₂ Γ) :
    C.secondCopy.embed C.center ∈ (𝓡∂ (n+1)).interior M := by
  let z := (C.charts.prod₂.coord C.center).1
  let B := C.coordinates.box
  let S := C.coordinates.second.shift
  have hCenter : (C.center : M) ∈ C.charts.prod₂.coord.source :=
    C.charts.source₂ ▸ C.charts.second.point_source
  have hz : C.charts.prod₂.coord C.center = (z, 0) :=
    Prod.ext rfl (C.charts.prod₂.height_eq_zero_on_boundary C.center.property hCenter)
  have hZ : (z, (0 : ℝ)) ∈ C.ambient :=
    B.support_inside ⟨Metric.mem_closedBall_self B.radius_pos.le,
      ⟨neg_nonpos.mpr B.radius_pos.le, B.radius_pos.le⟩⟩
  have hSCenter : (C.center : M) ∈ C.productSecond.coord.source :=
    ⟨hCenter, by change C.charts.prod₂.coord C.center ∈ C.ambient; rwa [hz]⟩
  have hPos : 0 < C.coordinates.height z := by
    change z ∈ {x | 0 < C.coordinates.height x}
    rw [C.coordinates.height_support]
    exact Metric.mem_ball_self B.radius_pos
  obtain ⟨hp, hRead⟩ := S.coordinateShift_spec C.center hSCenter
  have hCenterRead : C.productSecond.coord C.center = (z, 0) := hz
  rw [hCenterRead, C.coordinates.second.push_eq, C.coordinates.push_seam] at hRead
  rw [C.coordinates.second.embed_eq]
  exact (C.productSecond.interior_iff _ hp).mpr (hRead ▸ hPos)

/-- Relative closure of a boundary patch inside the compact original
manifold is compact in the boundary topology. -/
private theorem compact_relative_closure {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [CompactSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    (P : Set ((𝓡∂ n).boundary M)) : IsCompact (closure P) := by
  let : CompactSpace ((𝓡∂ n).boundary M) :=
    isCompact_iff_compactSpace.mp (((𝓡∂ n).isClosed_boundary (n := ∞) (by simp)).isCompact)
  exact isClosed_closure.isCompact

/-- Cap agreement of the actual inverse on a common chart source family
determines the Green kernels at every off-diagonal cap pair. -/
private theorem equalGreenOnCapOfSharedInverse {m : ℕ} {N₁ N₂ : Type*}
    [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁] [ConnectedSpace N₁]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₁] [IsManifold (J[m]) ∞ N₁]
    [MeasurableSpace N₁] [BorelSpace N₁]
    [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂] [ConnectedSpace N₂]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₂] [IsManifold (J[m]) ∞ N₂]
    [MeasurableSpace N₂] [BorelSpace N₂]
    (hn : 2 ≤ m+1) {D₁ : DirichletData m N₁} {D₂ : DirichletData m N₂}
    {cap : OpenPartialHomeomorph N₂ N₁}
    (hCapIso : IsLocalMetricIsometry D₁.metric D₂.metric cap)
    (hCap₁ : cap.target ⊆ (J[m]).interior N₁) (hCap₂ : cap.source ⊆ (J[m]).interior N₂)
    (hCapConn : IsConnected cap.source) (Q : NativeCapSourceCharts D₁ D₂ cap)
    {r₁ : NativeInverseRegularity D₁} {r₂ : NativeInverseRegularity D₂}
    (hAgree : NativeCapSourceAgreement Q r₁ r₂)
    {G₁ : N₁ × N₁ → ℝ} {G₂ : N₂ × N₂ → ℝ}
    (hG₁ : IsDirichletGreenKernel (J[m]) D₁.volume (nativeLaplace D₁.metric) G₁)
    (hG₂ : IsDirichletGreenKernel (J[m]) D₂.volume (nativeLaplace D₂.metric) G₂)
    (hRep₁ : RepresentsNativeInverse r₁ G₁) (hRep₂ : RepresentsNativeInverse r₂ G₂) :
    ∀ q ∈ cap.source, ∀ p ∈ cap.source, p ≠ q →
      G₁ (cap p, cap q) = G₂ (p, q) := by
  let E₁ (p : N₁) (f : 𝓓_{Q.support}(X (m+1), ℝ)) :=
    D₁.smoothInverse r₁ (smoothChartSource Q.first Q.closure_first f) p
  let E₂ (p : N₂) (f : 𝓓_{Q.support}(X (m+1), ℝ)) :=
    D₂.smoothInverse r₂ (smoothChartSource Q.second Q.closure_second f) p
  have hV₁ : Q.domain ⊆ Q.first.chart.target := subset_closure.trans Q.closure_first
  have hV₂ : Q.domain ⊆ Q.second.chart.target := subset_closure.trans Q.closure_second
  let R₁ := nativeCapSourceRepresentation r₁ Q.first (K := Q.support) Q.closure_first
    Q.open_domain Q.connected_domain subset_closure hG₁ hRep₁
  apply green_eqOn_of_capSourceRepresentations hn cap hCapIso hCap₂ hCap₁ hCapConn
    D₁.metric_volume D₂.metric_volume hG₁ hG₂ Q.first.chart Q.second.chart Q.open_domain
    Q.connected_domain hV₁ hV₂ (Q.closure_in_cap.mono subset_closure Subset.rfl)
    (Q.same_coordinates.mono subset_closure) E₁ E₂
    (fun p hp => funext fun f => hAgree p hp f)
    (chartVolume Q.first.metric) R₁.density_continuous R₁.density_positive
  intro φ hφ hc hs
  let f : 𝓓_{Q.support}(X (m+1), ℝ) :=
    ⟨φ, hφ, fun _ hx => image_eq_zero_of_notMem_tsupport (fun h => hx (subset_closure (hs h)))⟩
  refine ⟨f, fun p hp => ?_, fun p hp => ?_⟩
  · exact smoothInverse_chartTestSource_eq_greenIntegral r₁ Q.first hG₁ hRep₁ hV₁ hφ hc hs hp
  · refine (smoothInverse_chartTestSource_eq_greenIntegral r₂ Q.second hG₂ hRep₂
      hV₂ hφ hc hs hp).trans ?_
    apply setIntegral_congr_fun Q.open_domain.measurableSet
    intro x hx
    exact congrArg (fun t => φ x * G₂ (Q.second.chart.symm x, p) * t) (Q.same_density hx).symm

/-- Extend the released cap comparison to canonical inverse data for every
smooth pair whose forcings vanish off the caps and agree under identification. -/
private theorem inverse_agrees_on_signed_cap {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [ChartedSpace (EuclideanHalfSpace (m+1)) M]
    [IsManifold (J[m]) ∞ M] [MeasurableSpace M] [BorelSpace M]
    {d₁ d₂ : DirichletData m M} {Γ : Set ((J[m]).boundary M)}
    {C : MeasuredCommonCap d₁ d₂ Γ}
    (S : C.SignedInteriorCharts)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {μ₁ μ₂} (hμ₁ : IsMetricVolume C.firstMetric μ₁) (hμ₂ : IsMetricVolume C.secondMetric μ₂)
    (f₁ f₂ : Source[m, M])
    (hf₁ : tsupport (f₁ : M → ℝ) ⊆ C.capMap.target)
    (hf₂ : tsupport (f₂ : M → ℝ) ⊆ C.capMap.source)
    (hf : EqOn ((f₁ : M → ℝ) ∘ C.capMap) f₂ C.capMap.source) :
    EqOn (inverse[C.firstData μ₁ hμ₁] f₁ ∘ C.capMap)
      (inverse[C.secondData μ₂ hμ₂] f₂) C.capMap.source := by
  let D₁ := C.firstData μ₁ hμ₁
  let D₂ := C.secondData μ₂ hμ₂
  let w₁ := inverse[D₁] f₁
  let w₂ := inverse[D₂] f₂
  obtain ⟨hw₁,hz₁,hEq₁,_⟩ := D₁.smoothInverse_spec (nativeInverseRegularity D₁) f₁
  obtain ⟨hw₂,hz₂,hEq₂,_⟩ := D₂.smoothInverse_spec (nativeInverseRegularity D₂) f₂
  apply C.cap_solution_agreement S hEnergy hw₁ hw₂ hz₁ hz₂
  · intro x hx
    exact neg_eq_zero.mp ((hEq₁ hx.1).trans (image_eq_zero_of_notMem_tsupport
      (fun ht => hx.2 (subset_closure (hf₁ ht)))))
  · intro x hx
    exact neg_eq_zero.mp ((hEq₂ hx.1).trans (image_eq_zero_of_notMem_tsupport
      (fun ht => hx.2 (subset_closure (hf₂ ht)))))
  · intro x hx
    change nativeLaplace C.firstMetric w₁ (C.capMap x) = nativeLaplace C.secondMetric w₂ x
    apply neg_injective
    exact (hEq₁ (C.target_interior (C.capMap.map_source hx))).trans
      ((hf hx).trans (hEq₂ (C.source_interior hx)).symm)

/-- Proposition 2.2 of the September 24, 2026 manuscript. Both metrics
extend over the identified cap. The original boundary portion that
moves into the interior is compactly contained in the measured patch.
The actual kernels and canonical inverse solutions agree on the cap. -/
theorem proposition22 {m : ℕ} (hn : 3 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (J[m]) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (d₁ d₂ : DirichletData m M)
    {Γ : Set ((J[m]).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ) :
    ∃ C : MeasuredCommonCap d₁ d₂ Γ,
      ∃ P₀ : Set ((J[m]).boundary M),
        IsOpen P₀ ∧ P₀.Nonempty ∧ IsCompact (closure P₀) ∧ closure P₀ ⊆ Γ ∧
        (P₀ : Set ((J[m]).boundary M)) =
          {p : (J[m]).boundary M | C.secondCopy.embed (p : M) ∈ (J[m]).interior M} ∧
        ∃ (μ₁ μ₂ : Measure M) (hμ₁ : IsMetricVolume C.firstMetric μ₁)
            (hμ₂ : IsMetricVolume C.secondMetric μ₂) (G₁ G₂ : M × M → ℝ),
          IsDirichletGreenKernel (J[m]) μ₁ (nativeLaplace C.firstMetric) G₁ ∧
          IsDirichletGreenKernel (J[m]) μ₂ (nativeLaplace C.secondMetric) G₂ ∧
          RepresentsNativeInverse (nativeInverseRegularity (C.firstData μ₁ hμ₁)) G₁ ∧
          RepresentsNativeInverse (nativeInverseRegularity (C.secondData μ₂ hμ₂)) G₂ ∧
          (∀ p ∈ C.capMap.source, ∀ q ∈ C.capMap.source, p ≠ q →
            G₁ (C.capMap p, C.capMap q) = G₂ (p, q)) ∧
          ∀ (f₁ f₂ : Source[m, M]),
            tsupport (f₁ : M → ℝ) ⊆ C.capMap.target →
            tsupport (f₂ : M → ℝ) ⊆ C.capMap.source →
            EqOn ((f₁ : M → ℝ) ∘ C.capMap) f₂ C.capMap.source →
            EqOn (inverse[C.firstData μ₁ hμ₁] f₁ ∘ C.capMap)
              (inverse[C.secondData μ₂ hμ₂] f₂) C.capMap.source := by
  have hm : 2 ≤ m := by omega
  have hBoundary := (J[m]).isOpen_interior (M := M) (n := ∞) (by simp)
  obtain ⟨C⟩ := exists_attached_commonCap_of_patchEnergy hm d₁ d₂ hΓ hΓne hEnergy
  obtain ⟨S⟩ := C.exists_signedInteriorCharts
  obtain ⟨μ₁,hμ₁⟩ := exists_metricVolume_of_metricVolume d₁.metric C.firstMetric
    d₁.volume d₁.metric_volume
  obtain ⟨μ₂,hμ₂⟩ := exists_metricVolume_of_metricVolume d₂.metric C.secondMetric
    d₂.volume d₂.metric_volume
  let D₁ := C.firstData μ₁ hμ₁
  let D₂ := C.secondData μ₂ hμ₂
  let A₁ := S.firstMetricChart μ₁ hμ₁
  let A₂ := S.secondMetricChart μ₂ hμ₂
  obtain ⟨G₁,hG₁,hRep₁⟩ := exists_nativeCapGreenKernel D₁ (nativeInverseRegularity D₁)
  obtain ⟨G₂,hG₂,hRep₂⟩ := exists_nativeCapGreenKernel D₂ (nativeInverseRegularity D₂)
  let W := signedCap C.signedHeight
  have hW : IsOpen W := C.isOpen_signedCap
  have hW₁ : W ⊆ A₁.chart.target := by change W ⊆ S.first.target; rw [S.first_target]
  have hW₂ : W ⊆ A₂.chart.target := by change W ⊆ S.second.target; rw [S.second_target]
  have hMap : MapsTo A₂.chart.symm W C.capMap.source := by
    intro x hx
    change S.second.symm x ∈ C.capMap.source
    exact S.second_source ▸ S.second.map_target (S.second_target.symm ▸ hx)
  obtain ⟨q,hq⟩ := C.connected_source.nonempty
  let z := S.second q
  have hz : z ∈ W := by
    change S.second q ∈ signedCap C.signedHeight
    rw [← S.second_target]
    exact S.second.map_source (S.second_source.symm ▸ hq)
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
  let Q : NativeCapSourceCharts D₁ D₂ C.capMap :=
    NativeCapSourceCharts.of_ball A₁ A₂ hW₁ hW₂ hMap S.same_inverse S.same_field
      (half_pos hδ) ((closedBall_subset_ball (half_lt_self hδ)).trans hδW)
  have hAgree := MeasuredCommonCap.nativeCap_inverse_agreement hEnergy S hμ₁ hμ₂ Q
  have hGreen := equalGreenOnCapOfSharedInverse (show 2 ≤ m+1 by omega) C.isometry
    C.target_interior C.source_interior C.connected_source Q hAgree hG₁ hG₂ hRep₁ hRep₂
  let P : Set ((J[m]).boundary M) :=
    {p : (J[m]).boundary M | C.secondCopy.embed (p : M) ∈ (J[m]).interior M}
  have hOpen : IsOpen P :=
    hBoundary.preimage (C.secondCopy.smooth.continuous.comp continuous_subtype_val)
  refine ⟨C, P, hOpen, ⟨C.center, attachment_center C⟩, compact_relative_closure P,
    attachment_closure_subset C, rfl, μ₁, μ₂, hμ₁, hμ₂, G₁, G₂, hG₁, hG₂, hRep₁, hRep₂,
    (fun _ hp _ hq hpq => hGreen _ hq _ hp hpq),
    (fun f₁ f₂ => inverse_agrees_on_signed_cap S hEnergy hμ₁ hμ₂ f₁ f₂)⟩


end CalderonPaper
