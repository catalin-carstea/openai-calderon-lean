module

public import Proof.CalderonPatch.GlobalFromNativeCapSources

import Proof.CalderonPatch.InteriorIsometryNaturality
import Proof.CalderonPatch.NativeCapGreenKernel
import Proof.CalderonPatch.SmoothInteriorIsometry
import Proof.CalderonN.GreenRestriction
import Proof.CalderonN.GreenWeak

public section

open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Manifold
open CalderonN (X laplace_congrOn)
open CalderonPatch

namespace CalderonPaper

local notation "J[" m "]" => 𝓡∂ (m+1)
local notation "Source[" k "," N "]" => smoothSourceSubmodule (m := k) (M := N)
local notation "inverse[" D "]" => DirichletData.smoothInverse D (nativeInverseRegularity D)

section SharedSources
variable {m : ℕ} {N₁ N₂ : Type*}
    [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁] [ConnectedSpace N₁]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₁] [IsManifold (J[m]) ∞ N₁]
    [MeasurableSpace N₁] [BorelSpace N₁]
    [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂] [ConnectedSpace N₂]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₂] [IsManifold (J[m]) ∞ N₂]
    [MeasurableSpace N₂] [BorelSpace N₂]

omit [T2Space N₁] [CompactSpace N₁] [ConnectedSpace N₁]
  [T2Space N₂] [CompactSpace N₂] [ConnectedSpace N₂] in
/-- In any open source region inside the second cap there are common
transported coordinate balls for the paired native test family. -/
private theorem exists_shared_source_ball {D₁ : DirichletData m N₁} {D₂ : DirichletData m N₂}
    {cap : OpenPartialHomeomorph N₂ N₁}
    (hCapIso : IsLocalMetricIsometry D₁.metric D₂.metric cap)
    (hCap₁ : cap.target ⊆ (J[m]).interior N₁) (hCap₂ : cap.source ⊆ (J[m]).interior N₂)
    {U : Set N₂} (hOpen : IsOpen U) (hNonempty : U.Nonempty) (hInside : U ⊆ cap.source) :
    ∃ Q : NativeCapSourceCharts D₁ D₂ cap, Q.second.chart.symm '' (Q.support : Set _) ⊆ U := by
  obtain ⟨p,hp⟩ := hNonempty
  obtain ⟨b,hpb,hbU,hbI,hb,hbs⟩ := exists_interiorChart p (hCap₂ (hInside hp)) hOpen hp
  have hbCap : b.source ⊆ cap.source := hbU.trans hInside
  obtain ⟨a,haT,haS,haInv,ha,has,hMetric⟩ := exists_transported_chart hCapIso b hbCap hb hbs
  have haI : a.source ⊆ (J[m]).interior N₁ := by
    rw [haS]
    rintro _ ⟨q,hq,rfl⟩
    exact hCap₁ (cap.map_source (hbCap hq))
  let A₁ := nativeInteriorMetricChart D₁.metric D₁.volume D₁.metric_volume a haI ha has
  let A₂ := nativeInteriorMetricChart D₂.metric D₂.volume D₂.metric_volume b hbI hb hbs
  have haTarget : b.target ⊆ A₁.chart.target := by change b.target ⊆ a.target; rw [haT]
  have hbTarget : b.target ⊆ A₂.chart.target := Subset.rfl
  have hMap : MapsTo A₂.chart.symm b.target cap.source :=
    fun _ hx => hbCap (b.map_target hx)
  have hCoordinates : EqOn A₁.chart.symm (cap ∘ A₂.chart.symm) b.target :=
    fun x _ => congrFun haInv x
  obtain ⟨s,hs,hBall⟩ := Metric.mem_nhds_iff.mp (b.open_target.mem_nhds (b.map_source hpb))
  let Q := NativeCapSourceCharts.of_ball A₁ A₂ haTarget hbTarget hMap hCoordinates hMetric
    (half_pos hs) ((closedBall_subset_ball (half_lt_self hs)).trans hBall)
  refine ⟨Q, ?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact hbU (b.map_target (Q.closure_second hx))

omit [CompactSpace N₁] [ConnectedSpace N₁] [BorelSpace N₁]
  [CompactSpace N₂] [ConnectedSpace N₂] [BorelSpace N₂] in
/-- Every common coordinate label is a pair of native sources supported
in the prescribed common source sets. -/
private theorem shared_source_ball_support {D₁ : DirichletData m N₁} {D₂ : DirichletData m N₂}
    {cap : OpenPartialHomeomorph N₂ N₁} (Q : NativeCapSourceCharts D₁ D₂ cap)
    {U : Set N₂} (hU : Q.second.chart.symm '' (Q.support : Set _) ⊆ U)
    (f : 𝓓_{Q.support}(X (m+1), ℝ)) :
    tsupport (smoothChartSource Q.first Q.closure_first f : N₁ → ℝ) ⊆ cap '' U ∧
    tsupport (smoothChartSource Q.second Q.closure_second f : N₂ → ℝ) ⊆ U := by
  constructor
  · change tsupport (CalderonN.chartTest Q.first.chart f) ⊆ cap '' U
    have hS := (CalderonN.tsupport_chartTest_subset Q.first.chart f.compact_supp
      (f.tsupport_subset.trans Q.closure_first)).trans (image_mono f.tsupport_subset)
    refine hS.trans ?_
    rw [Q.image_support_first, ← Q.image_support_second]
    exact image_mono hU
  · change tsupport (CalderonN.chartTest Q.second.chart f) ⊆ U
    exact (CalderonN.tsupport_chartTest_subset Q.second.chart f.compact_supp
      (f.tsupport_subset.trans Q.closure_second)).trans ((image_mono f.tsupport_subset).trans hU)

omit [T2Space N₁] [CompactSpace N₁] [ConnectedSpace N₁] [MeasurableSpace N₁] [BorelSpace N₁]
  [T2Space N₂] [CompactSpace N₂] [ConnectedSpace N₂] [MeasurableSpace N₂] [BorelSpace N₂] in
/-- Paired forcings supported in the same region continue to agree after
extending the cap identification by an injective interior map. -/
private theorem paired_forcing_eq_of_cap_extension {cap e : OpenPartialHomeomorph N₂ N₁}
    {U : Set N₂} (hU : U ⊆ cap.source) (hCap : cap.source ⊆ e.source)
    (hExtend : EqOn e cap cap.source)
    {f₁ : N₁ → ℝ} {f₂ : N₂ → ℝ}
    (h₁ : tsupport f₁ ⊆ cap '' U) (h₂ : tsupport f₂ ⊆ U)
    (hf : EqOn (f₁ ∘ cap) f₂ U) :
    EqOn (f₁ ∘ e) f₂ e.source := by
  intro x hx
  by_cases h : x ∈ U
  · change f₁ (e x) = f₂ x
    rw [hExtend (hU h)]
    exact hf h
  · have h₁' : e x ∉ tsupport f₁ := by
      intro hs
      obtain ⟨y,hy,heq⟩ := h₁ hs
      have he : e y = e x := (hExtend (hU hy)).trans heq
      exact h ((e.injOn (hCap (hU hy)) hx he) ▸ hy)
    exact (image_eq_zero_of_notMem_tsupport h₁').trans
      (image_eq_zero_of_notMem_tsupport (fun hs => h (h₂ hs))).symm

end SharedSources

/-- The native Laplacian is local on open subsets of the interior. -/
private theorem nativeLaplace_eq_of_eqOn {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    (g : SmoothMetric n M) {U : Set M}
    (hU : IsOpen U) (hI : U ⊆ (𝓡∂ n).interior M)
    {u v : M → ℝ} (hu : ContMDiffOn (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ u U)
    (hv : ContMDiffOn (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v U) (hEq : EqOn u v U) :
    EqOn (nativeLaplace g u) (nativeLaplace g v) U := by
  intro p hp
  obtain ⟨e, hpe, heU, heI, he, hes⟩ := exists_interiorChart p (hI hp) hU hp
  rw [nativeLaplace_eq_coordinate g e heI he hes (hu.mono heU) hpe,
    nativeLaplace_eq_coordinate g e heI he hes (hv.mono heU) hpe]
  exact laplace_congrOn e.open_target (fun _ _ => rfl)
    (fun x hx => hEq (heU (e.map_target hx))) (e.map_source hpe)

/-- A smooth completion of an interior isometry intertwines the smooth
Dirichlet inverses on sources that match under the interior map. -/
private theorem inverse_eq_of_completed_isometry {m : ℕ} {N₁ N₂ : Type*}
    [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁] [ConnectedSpace N₁]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₁] [IsManifold (J[m]) ∞ N₁]
    [MeasurableSpace N₁] [BorelSpace N₁]
    [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂] [ConnectedSpace N₂]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₂] [IsManifold (J[m]) ∞ N₂]
    [MeasurableSpace N₂] [BorelSpace N₂]
    (D₁ : DirichletData m N₁) (D₂ : DirichletData m N₂)
    (e : OpenPartialHomeomorph N₂ N₁)
    (hSource : e.source = (J[m]).interior N₂) (hTarget : e.target = (J[m]).interior N₁)
    (he : IsLocalMetricIsometry D₁.metric D₂.metric e)
    (F : N₂ ≃ₘ⟮J[m], J[m]⟯ N₁) (hF : EqOn F e e.source)
    (f₁ : Source[m, N₁]) (f₂ : Source[m, N₂])
    (hf : EqOn ((f₁ : N₁ → ℝ) ∘ e) f₂ e.source) :
    EqOn (inverse[D₁] f₁ ∘ e) (inverse[D₂] f₂) e.source := by
  let u₁ := inverse[D₁] f₁
  let v := u₁ ∘ F
  obtain ⟨hu₁, huBoundary, huEq, _⟩ := D₁.smoothInverse_spec (nativeInverseRegularity D₁) f₁
  have hv : ContMDiff (J[m]) 𝓘(ℝ, ℝ) ∞ v := hu₁.comp F.contMDiff
  have hvBoundary : EqOn v 0 ((J[m]).boundary N₂) := by
    intro x hx
    apply huBoundary
    change x ∈ F ⁻¹' (J[m]).boundary N₁
    rwa [F.preimage_boundary (by simp)]
  let V : DirichletTest D₂ := DirichletTest.ofSmooth v hv hvBoundary
  have hLaplaceEq : EqOn (nativeLaplace D₂.metric v)
      (nativeLaplace D₂.metric (u₁ ∘ e)) e.source :=
    nativeLaplace_eq_of_eqOn D₂.metric e.open_source (le_of_eq hSource)
      hv.contMDiffOn (hu₁.comp_contMDiffOn he.smooth) (fun x hx => congrArg u₁ (hF hx))
  have hAE : ∀ᵐ x ∂D₂.volume, x ∈ (J[m]).interior N₂ := by
    rw [ae_iff]
    change D₂.volume ((J[m]).interior N₂)ᶜ = 0
    rw [(J[m]).compl_interior]
    exact metricVolume_boundary_eq_zero D₂.metric D₂.volume D₂.metric_volume
  have hV : (f₂ : N₂ → ℝ) =ᵐ[D₂.volume] -nativeLaplace D₂.metric (V : N₂ → ℝ) := by
    filter_upwards [hAE] with x hx
    have hxS : x ∈ e.source := hSource.symm ▸ hx
    change f₂ x = -nativeLaplace D₂.metric v x
    rw [hLaplaceEq hxS, nativeLaplace_comp_localIsometry he
      (le_of_eq hSource) (le_of_eq hTarget) hu₁.contMDiffOn hxS]
    exact (hf hxS).symm.trans (huEq (hTarget ▸ e.map_source hxS)).symm
  have hInverse := smoothInverse_eq_dirichletTest_of_ae (nativeInverseRegularity D₂) V hV
  intro x hx
  change u₁ (e x) = inverse[D₂] f₂ x
  rw [hInverse]
  change u₁ (e x) = u₁ (F x)
  rw [hF hx]

/-- Proposition 7.1 of the September 24, 2026 manuscript. The identified
cap and the common supported source evaluations are extended by one
surjective isometry of the interiors. -/
theorem proposition71 {m : ℕ} (hn : 3 ≤ m + 1) {N₁ N₂ : Type*}
    [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁] [ConnectedSpace N₁]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₁] [IsManifold (J[m]) ∞ N₁]
    [MeasurableSpace N₁] [BorelSpace N₁]
    [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂] [ConnectedSpace N₂]
    [ChartedSpace (EuclideanHalfSpace (m+1)) N₂] [IsManifold (J[m]) ∞ N₂]
    [MeasurableSpace N₂] [BorelSpace N₂]
    (D₁ : DirichletData m N₁) (D₂ : DirichletData m N₂)
    (cap : OpenPartialHomeomorph N₂ N₁)
    (hCapIso : IsLocalMetricIsometry D₁.metric D₂.metric cap)
    (hCap₁ : cap.target ⊆ (J[m]).interior N₁) (hCap₂ : cap.source ⊆ (J[m]).interior N₂)
    (hCapConn : IsConnected cap.source)
    (U₀ : Set N₂) (hOpen : IsOpen U₀) (hNonempty : U₀.Nonempty)
    (hCompact : IsCompact (closure U₀)) (hInside : closure U₀ ⊆ cap.source)
    (hAgreement : ∀ (f₁ : Source[m, N₁]) (f₂ : Source[m, N₂]),
      tsupport (f₁ : N₁ → ℝ) ⊆ cap '' U₀ → tsupport (f₂ : N₂ → ℝ) ⊆ U₀ →
      EqOn ((f₁ : N₁ → ℝ) ∘ cap) f₂ U₀ →
      EqOn (inverse[D₁] f₁ ∘ cap) (inverse[D₂] f₂) cap.source) :
    ∃ Φ : OpenPartialHomeomorph N₂ N₁,
      Φ.source = (J[m]).interior N₂ ∧ Φ.target = (J[m]).interior N₁ ∧
      IsLocalMetricIsometry D₁.metric D₂.metric Φ ∧ EqOn Φ cap cap.source ∧
      ∀ (f₁ : Source[m, N₁]) (f₂ : Source[m, N₂]),
        tsupport (f₁ : N₁ → ℝ) ⊆ cap '' U₀ → tsupport (f₂ : N₂ → ℝ) ⊆ U₀ →
        EqOn ((f₁ : N₁ → ℝ) ∘ cap) f₂ U₀ →
        EqOn (inverse[D₁] f₁ ∘ Φ) (inverse[D₂] f₂) Φ.source := by
  have hUCap : U₀ ⊆ cap.source := subset_closure.trans hInside
  obtain ⟨Q,hQ⟩ := exists_shared_source_ball hCapIso hCap₁ hCap₂ hOpen hNonempty hUCap
  have hAgree : NativeCapSourceAgreement Q (nativeInverseRegularity D₁)
      (nativeInverseRegularity D₂) := by
    intro p hp f
    obtain ⟨hf₁,hf₂⟩ := shared_source_ball_support Q hQ f
    exact (hAgreement _ _ hf₁ hf₂ (fun x hx => (Q.source_eqOn f (hUCap hx)).symm) hp).symm
  obtain ⟨e,hSource,hTarget,he,hExtend⟩ := exists_globalInteriorIsometry_of_capInverseAgreement
    Q hn hCapIso hCap₁ hCap₂ hCapConn.isPreconnected hAgree
  obtain ⟨F,hF,_⟩ := smoothCompletion_of_interiorIsometry he hSource hTarget
  refine ⟨e,hSource,hTarget,he,hExtend,?_⟩
  intro f₁ f₂ hf₁ hf₂ hf
  have hCapSource : cap.source ⊆ e.source := hSource.symm ▸ hCap₂
  exact inverse_eq_of_completed_isometry D₁ D₂ e hSource hTarget he F hF f₁ f₂
    (paired_forcing_eq_of_cap_extension hUCap hCapSource hExtend hf₁ hf₂ hf)


end CalderonPaper
