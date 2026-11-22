module

public import Proof.CalderonPatch.NativeCapSourceJets
public import Proof.CalderonPatch.GlobalFromSources
public import Proof.CalderonPatch.NativeInverseRegularityProof

import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Manifold Matrix.Norms.Elementwise Topology

namespace CalderonPatch

open CalderonN (X InteriorMetricChart chartVolume)

variable {m : ℕ} {M₁ M₂ : Type*}
  [TopologicalSpace M₁]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M₁] [IsManifold (𝓡∂ (m+1)) ∞ M₁]
  [MeasurableSpace M₁]
  [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M₂] [IsManifold (𝓡∂ (m+1)) ∞ M₂]
  [MeasurableSpace M₂]

local notation "J" => 𝓡∂ (m+1)
local notation "Y" => X (m+1)

/-- The paired metric charts and one connected open support domain in the cap.
The closure of the support lies in both charts and in the common cap map. -/
structure NativeCapSourceCharts (D₁ : DirichletData m M₁) (D₂ : DirichletData m M₂)
    (Φ : OpenPartialHomeomorph M₂ M₁) where
  first : InteriorMetricChart J D₁.volume (nativeLaplace D₁.metric)
  second : InteriorMetricChart J D₂.volume (nativeLaplace D₂.metric)
  domain : Set Y
  open_domain : IsOpen domain
  connected_domain : IsConnected domain
  compact_closure : IsCompact (closure domain)
  closure_first : closure domain ⊆ first.chart.target
  closure_second : closure domain ⊆ second.chart.target
  closure_in_cap : MapsTo second.chart.symm (closure domain) Φ.source
  same_coordinates : EqOn first.chart.symm (Φ ∘ second.chart.symm) (closure domain)
  same_density : EqOn (chartVolume first.metric) (chartVolume second.metric) domain

variable {D₁ : DirichletData m M₁} {D₂ : DirichletData m M₂}
variable {Φ : OpenPartialHomeomorph M₂ M₁}
variable (C : NativeCapSourceCharts D₁ D₂ Φ)

namespace NativeCapSourceCharts

/-- A ball with closure in matched coordinates gives a common support domain. -/
@[expose] def of_ball
    (A₁ : InteriorMetricChart J D₁.volume (nativeLaplace D₁.metric))
    (A₂ : InteriorMetricChart J D₂.volume (nativeLaplace D₂.metric))
    {W : Set Y} (hW₁ : W ⊆ A₁.chart.target) (hW₂ : W ⊆ A₂.chart.target)
    (hCap : MapsTo A₂.chart.symm W Φ.source)
    (hCoordinates : EqOn A₁.chart.symm (Φ ∘ A₂.chart.symm) W)
    (hMetric : EqOn A₁.metric A₂.metric W)
    {z : Y} {r : ℝ} (hr : 0 < r) (hBall : closedBall z r ⊆ W) :
    NativeCapSourceCharts D₁ D₂ Φ where
  first := A₁
  second := A₂
  domain := ball z r
  open_domain := isOpen_ball
  connected_domain := (convex_ball z r).isConnected ⟨z,mem_ball_self hr⟩
  compact_closure := by rw [closure_ball _ hr.ne']; exact isCompact_closedBall _ _
  closure_first := by rw [closure_ball _ hr.ne']; exact hBall.trans hW₁
  closure_second := by rw [closure_ball _ hr.ne']; exact hBall.trans hW₂
  closure_in_cap := by rw [closure_ball _ hr.ne']; exact hCap.mono hBall Subset.rfl
  same_coordinates := by rw [closure_ball _ hr.ne']; exact hCoordinates.mono hBall
  same_density x hx := congrArg (fun γ : CalderonN.Mat (m+1) => Real.sqrt γ.det)
    (hMetric (hBall (ball_subset_closedBall hx)))

/-- Every label is supported in the same compact closure of the source domain. -/
@[expose] def support : Compacts Y := ⟨closure C.domain,C.compact_closure⟩

variable [T2Space M₂]

theorem image_support_second : C.second.chart.symm '' (C.support : Set Y) =
    closure (C.second.chart.symm '' C.domain) := by
  have hc := C.second.chart.continuousOn_symm.mono C.closure_second
  exact Subset.antisymm hc.image_closure
    (closure_minimal (image_mono subset_closure) (C.compact_closure.image_of_continuousOn hc).isClosed)

theorem image_support_first : C.first.chart.symm '' (C.support : Set Y) =
    Φ '' closure (C.second.chart.symm '' C.domain) := by
  rw [← C.image_support_second, image_image]
  exact C.same_coordinates.image_eq

end NativeCapSourceCharts

variable [T2Space M₁] [T2Space M₂]

/-- The paired native forcings agree at every matched cap point. -/
theorem NativeCapSourceCharts.source_eqOn (f : 𝓓_{C.support}(Y, ℝ)) :
    EqOn (smoothChartSource C.second C.closure_second f : M₂ → ℝ)
      ((smoothChartSource C.first C.closure_first f : M₁ → ℝ) ∘ Φ) Φ.source := by
  intro p hp
  by_cases hpS : p ∈ C.second.chart.symm '' (C.support : Set Y)
  · obtain ⟨z,hz,rfl⟩ := hpS
    change CalderonN.chartTest C.second.chart f (C.second.chart.symm z) =
      CalderonN.chartTest C.first.chart f (Φ (C.second.chart.symm z))
    have hCoord : C.first.chart.symm z = Φ (C.second.chart.symm z) := C.same_coordinates hz
    rw [← hCoord]
    exact (chartTest_comp_inverse C.second.chart f (C.closure_second hz)).trans
      (chartTest_comp_inverse C.first.chart f (C.closure_first hz)).symm
  · have hpF : Φ p ∉ C.first.chart.symm '' (C.support : Set Y) := by
      rintro ⟨z,hz,hEq⟩
      have he : Φ (C.second.chart.symm z) = Φ p := (C.same_coordinates hz).symm.trans hEq
      exact hpS ⟨z,hz,Φ.injOn (C.closure_in_cap hz) hp he⟩
    exact (smoothChartSource_eq_zero_off C.second C.closure_second f hpS).trans
      (smoothChartSource_eq_zero_off C.first C.closure_first f hpF).symm

omit [T2Space M₂] in
/-- The paired first forcing vanishes off the target of the common cap. -/
theorem NativeCapSourceCharts.source_first_eq_zero_off_cap (f : 𝓓_{C.support}(Y, ℝ))
    {p : M₁} (hp : p ∉ Φ.target) : smoothChartSource C.first C.closure_first f p = 0 := by
  apply smoothChartSource_eq_zero_off
  rintro ⟨z,hz,rfl⟩
  apply hp
  rw [C.same_coordinates hz]
  exact Φ.map_source (C.closure_in_cap hz)

omit [T2Space M₁] in
/-- The paired second forcing vanishes off the source of the common cap. -/
theorem NativeCapSourceCharts.source_second_eq_zero_off_cap (f : 𝓓_{C.support}(Y, ℝ))
    {p : M₂} (hp : p ∉ Φ.source) : smoothChartSource C.second C.closure_second f p = 0 := by
  apply smoothChartSource_eq_zero_off
  rintro ⟨z,hz,rfl⟩
  exact hp (C.closure_in_cap hz)

variable [CompactSpace M₁] [ConnectedSpace M₁] [BorelSpace M₁]
  [CompactSpace M₂] [ConnectedSpace M₂] [BorelSpace M₂]

/-- Agreement of the canonical inverses for each identical coordinate label
throughout the actual common cap. -/
@[expose] def NativeCapSourceAgreement (h₁ : NativeInverseRegularity D₁) (h₂ : NativeInverseRegularity D₂) : Prop :=
  ∀ p ∈ Φ.source, ∀ f : 𝓓_{C.support}(Y, ℝ),
    D₂.smoothInverse h₂ (smoothChartSource C.second C.closure_second f) p =
      D₁.smoothInverse h₁ (smoothChartSource C.first C.closure_first f) (Φ p)

/-- The shared cap solutions and their actual Green kernels determine one
interior isometry extending the supplied cap isometry. -/
theorem exists_globalInteriorIsometry_of_nativeCapSources (hn : 3 ≤ m+1)
    (h₁ : NativeInverseRegularity D₁) (h₂ : NativeInverseRegularity D₂)
    (hIso : IsLocalMetricIsometry D₁.metric D₂.metric Φ)
    (hI₁ : Φ.target ⊆ (J).interior M₁) (hI₂ : Φ.source ⊆ (J).interior M₂)
    (hConn : IsPreconnected Φ.source)
    (hAgreement : NativeCapSourceAgreement C h₁ h₂) :
    ∃ e : OpenPartialHomeomorph M₂ M₁,
      e.source = (J).interior M₂ ∧ e.target = (J).interior M₁ ∧
        IsLocalMetricIsometry D₁.metric D₂.metric e ∧ EqOn e Φ Φ.source := by
  let : LocallyConnectedSpace M₂ := ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace (m+1)) M₂
  obtain ⟨G₁,hG₁,hRep₁⟩ := exists_nativeCapGreenKernel D₁ h₁
  obtain ⟨G₂,hG₂,hRep₂⟩ := exists_nativeCapGreenKernel D₂ h₂
  have hn' : 2 ≤ m+1 := by omega
  have hK₁ : (C.support : Set Y) ⊆ C.first.chart.target := C.closure_first
  have hK₂ : (C.support : Set Y) ⊆ C.second.chart.target := C.closure_second
  have hVK : C.domain ⊆ (C.support : Set Y) := subset_closure
  let Q₁ := nativeCapSourceRepresentation h₁ C.first hK₁ C.open_domain
    C.connected_domain hVK hG₁ hRep₁
  let Q₂ := nativeCapSourceRepresentation h₂ C.second hK₂ C.open_domain
    C.connected_domain hVK hG₂ hRep₂
  let E₁ := sourceEvaluations_of_capSolutions hn' D₁.metric_volume Q₁ hG₁
    (continuous_pi fun f => (nativeCapSolution_smooth h₁ C.first C.closure_first f).continuous)
    (fun _ hx => funext fun f => nativeCapSolution_zero_trace h₁ C.first C.closure_first f hx)
  let E₂ := sourceEvaluations_of_capSolutions hn' D₂.metric_volume Q₂ hG₂
    (continuous_pi fun f => (nativeCapSolution_smooth h₂ C.second C.closure_second f).continuous)
    (fun _ hx => funext fun f => nativeCapSolution_zero_trace h₂ C.second C.closure_second f hx)
  let Seed : EvaluationMatch E₂ E₁ (IsLocalMetricIsometry D₁.metric D₂.metric) :=
    ⟨Φ,hI₂,hI₁,fun p hp => funext fun f => hAgreement p hp f,hIso⟩
  let Sources : CommonCapSources E₂ E₁ Seed G₁ G₂ :=
    { first := C.first.chart
      second := C.second.chart
      domain := C.domain
      open_domain := C.open_domain
      connected_domain := C.connected_domain
      first_target := subset_closure.trans C.closure_first
      second_target := subset_closure.trans C.closure_second
      source_closure := by
        rw [← C.image_support_second]
        exact image_subset_iff.mpr C.closure_in_cap
      same_coordinates := C.same_coordinates.mono subset_closure
      density := chartVolume C.first.metric
      density_continuous := Q₁.density_continuous
      density_pos := Q₁.density_positive
      representation := by
        intro φ hφ hc hSupp
        let f : 𝓓_{C.support}(Y, ℝ) := ⟨φ,hφ,fun _ hx =>
          image_eq_zero_of_notMem_tsupport (fun ht => hx (subset_closure (hSupp ht)))⟩
        refine ⟨f,fun p hp => ?_,fun p hp => ?_⟩
        · exact smoothInverse_chartTestSource_eq_greenIntegral h₁ C.first hG₁ hRep₁
            (subset_closure.trans C.closure_first) hφ hc hSupp hp
        · refine (smoothInverse_chartTestSource_eq_greenIntegral h₂ C.second hG₂ hRep₂
            (subset_closure.trans C.closure_second) hφ hc hSupp hp).trans ?_
          apply setIntegral_congr_fun C.open_domain.measurableSet
          intro x hx
          exact congrArg (fun t => φ x * G₂ (C.second.chart.symm x,p) * t)
            (C.same_density hx).symm }
  have hH₁ (f : 𝓓_{C.support}(Y, ℝ)) :
      EqOn (nativeLaplace D₁.metric (fun x => E₁.value x f)) 0
        ((J).interior M₁ \ (Seed.chart '' closure (Sources.second.symm '' Sources.domain))) := by
    change EqOn (nativeLaplace D₁.metric (nativeCapSolutionLinear h₁ C.first C.closure_first f)) 0
      ((J).interior M₁ \ (Φ '' closure (C.second.chart.symm '' C.domain)))
    rw [← C.image_support_first]
    exact nativeCapSolution_harmonic_off h₁ C.first C.closure_first f
  have hH₂ (f : 𝓓_{C.support}(Y, ℝ)) :
      EqOn (nativeLaplace D₂.metric (fun x => E₂.value x f)) 0
        ((J).interior M₂ \ closure (Sources.second.symm '' Sources.domain)) := by
    change EqOn (nativeLaplace D₂.metric (nativeCapSolutionLinear h₂ C.second C.closure_second f)) 0
      ((J).interior M₂ \ closure (C.second.chart.symm '' C.domain))
    rw [← C.image_support_second]
    exact nativeCapSolution_harmonic_off h₂ C.second C.closure_second f
  obtain ⟨z,hz⟩ := C.connected_domain.nonempty
  have hSeed : C.second.chart.symm z ∈ Seed.chart.source := C.closure_in_cap (subset_closure hz)
  have hConn₁ : IsConnected E₁.interior := isConnected_manifoldInterior
  have hConn₂ : IsConnected E₂.interior := isConnected_manifoldInterior
  obtain ⟨e,heI₂,heI₁,heIso,_,heAgree⟩ := exists_globalInteriorIsometry_of_cap_sources hn
    E₂ E₁ rfl rfl hConn₂ hConn₁ D₁.metric D₂.metric D₁.metric_volume D₂.metric_volume hG₁ hG₂
    Seed hConn hSeed Sources (nativeCapSolution_smooth h₁ C.first C.closure_first)
    (nativeCapSolution_smooth h₂ C.second C.closure_second) hH₁ hH₂ (by
      intro p hp B
      change p ∈ (J).interior M₂ \ closure (C.second.chart.symm '' C.domain) at hp
      rw [← C.image_support_second] at hp
      exact exists_nativeCapSolution_mfderiv h₂ C.second C.closure_second C.open_domain
        C.connected_domain hVK hG₂ hRep₂ hn' hp B) (by
      intro a ha haS haI haH x hx S
      change a.source ⊆ (J).interior M₁ \ (Φ '' closure (C.second.chart.symm '' C.domain)) at ha
      rw [← C.image_support_first] at ha
      exact nativeCapSolution_hessianSpan h₁ C.first C.closure_first C.open_domain
        C.connected_domain hVK hG₁ hRep₁ hn' a ha haS haI haH hx S)
  exact ⟨e,heI₂,heI₁,heIso,heAgree Seed⟩

/-- With native regularity supplied by the canonical weak inverse, agreement
of the common cap solutions yields one global interior isometry. -/
theorem exists_globalInteriorIsometry_of_capInverseAgreement (hn : 3 ≤ m+1)
    (hIso : IsLocalMetricIsometry D₁.metric D₂.metric Φ)
    (hI₁ : Φ.target ⊆ (J).interior M₁) (hI₂ : Φ.source ⊆ (J).interior M₂)
    (hConn : IsPreconnected Φ.source)
    (hAgreement : NativeCapSourceAgreement C (nativeInverseRegularity D₁) (nativeInverseRegularity D₂)) :
    ∃ e : OpenPartialHomeomorph M₂ M₁,
      e.source = (J).interior M₂ ∧ e.target = (J).interior M₁ ∧
        IsLocalMetricIsometry D₁.metric D₂.metric e ∧ EqOn e Φ Φ.source :=
  exists_globalInteriorIsometry_of_nativeCapSources C hn
    (nativeInverseRegularity D₁) (nativeInverseRegularity D₂) hIso hI₁ hI₂ hConn hAgreement

end CalderonPatch
