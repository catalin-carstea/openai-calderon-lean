module

public import Proof.CalderonPatch.OffPoleJetHarmonic
public import Proof.CalderonPatch.ChartDensity

import Proof.CalderonN.GreenRestriction
import Mathlib.MeasureTheory.Measure.AEMeasurable

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X Harmonic InteriorMetricChart IsDirichletGreenKernel parameterSecondOrder chartVolumeMeasure)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- The joint Green function in two interior charts is smooth on
every product whose two coordinate images are disjoint. -/
theorem contDiffOn_jointGreen_of_disjoint_charts {μ : Measure M} {L : (M → ℝ) → M → ℝ}
    {G : M × M → ℝ} (hG : IsDirichletGreenKernel J μ L G)
    (A C : InteriorMetricChart J μ L) {U V : Set (X n)}
    (hU : U ⊆ A.chart.target) (hV : V ⊆ C.chart.target)
    (hDis : ∀ x ∈ U, ∀ z ∈ V, A.chart.symm x ≠ C.chart.symm z) :
    ContDiffOn ℝ ∞ (Function.uncurry fun x z => G (A.chart.symm x, C.chart.symm z)) (U ×ˢ V) := by
  have hF : ContMDiffOn ((K).prod K) ((J).prod J) ∞
      (fun p : X n × X n => (A.chart.symm p.1, C.chart.symm p.2)) (U ×ˢ V) :=
    ((A.smooth_inverse.mono hU).comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)).prodMk
      ((C.smooth_inverse.mono hV).comp contMDiff_snd.contMDiffOn (fun _ hx => hx.2))
  have hMap : MapsTo (fun p : X n × X n => (A.chart.symm p.1, C.chart.symm p.2)) (U ×ˢ V)
      {p | p.1 ∈ (J).interior M ∧ p.2 ∈ (J).interior M ∧ p.1 ≠ p.2} := fun _ hp =>
    ⟨A.source_interior (A.chart.map_target (hU hp.1)),
      C.source_interior (C.chart.map_target (hV hp.2)), hDis _ hp.1 _ hp.2⟩
  have H := hG.smooth_off_diagonal.comp hF hMap
  rw [chartedSpaceSelf_prod, ← modelWithCornersSelf_prod] at H
  exact H.contDiffOn

/-- Compact coordinate source support separated from an interior
pole remains separated on an open rectangle of coordinate pairs. -/
theorem exists_green_chart_rectangle {μ : Measure M} {L : (M → ℝ) → M → ℝ}
    (A C : InteriorMetricChart J μ L) {U T : Set (X n)} (hU : IsOpen U) (hUA : U ⊆ A.chart.target)
    (hT : IsCompact T) (hTU : T ⊆ U) {z : X n} (hz : z ∈ C.chart.target)
    (hApart : C.chart.symm z ∉ A.chart.symm '' T) :
    ∃ U' V : Set (X n), IsOpen U' ∧ IsOpen V ∧ T ⊆ U' ∧ U' ⊆ U ∧
      z ∈ V ∧ V ⊆ C.chart.target ∧ ∀ x ∈ U', ∀ s ∈ V, A.chart.symm x ≠ C.chart.symm s := by
  have hK : IsCompact (A.chart.symm '' T) := hT.image_of_continuousOn
    (A.chart.continuousOn_symm.mono (hTU.trans hUA))
  obtain ⟨N₁,N₂,hN₁,hN₂,hTN₁,hzN₂,hNN⟩ := hK.separation_of_notMem hApart
  let U' := U ∩ A.chart.symm ⁻¹' N₁
  let V := C.chart.target ∩ C.chart.symm ⁻¹' N₂
  refine ⟨U',V,(A.chart.continuousOn_symm.mono hUA).isOpen_inter_preimage hU hN₁,
    C.chart.continuousOn_symm.isOpen_inter_preimage C.chart.open_target hN₂,
    fun x hx => ⟨hTU hx,hTN₁ (mem_image_of_mem _ hx)⟩, inter_subset_left,
    ⟨hz,hzN₂⟩, inter_subset_left, ?_⟩
  exact fun _ hx _ hs => Disjoint.ne_of_mem hNN hx.2 hs.2

/-- Differentiating a Green kernel at an interior pole gives a
smooth harmonic representative in every chart away from that pole. -/
theorem harmonic_greenParameterJet_off_pole {g : SmoothMetric n M} {μ : Measure M}
    {G : M × M → ℝ} (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (C A : InteriorMetricChart J μ (nativeLaplace g)) {z : X n} (hz : z ∈ C.chart.target)
    (hApart : C.chart.symm z ∉ A.chart.source)
    (a : I n → I n → ℝ) (b : I n → ℝ) (c : ℝ) :
    Harmonic A.chart.target A.metric
      (fun x => parameterSecondOrder a b c (fun s => G (A.chart.symm x, C.chart.symm s)) z) := by
  let w := fun x => parameterSecondOrder a b c (fun s => G (A.chart.symm x, C.chart.symm s)) z
  have hLocal (x : X n) (hx : x ∈ A.chart.target) :
      ∃ U : Set (X n), IsOpen U ∧ x ∈ U ∧ U ⊆ A.chart.target ∧ Harmonic U A.metric w := by
    have hNe : A.chart.symm x ≠ C.chart.symm z :=
      fun h => hApart (h ▸ A.chart.map_target hx)
    let O : Set (X n × X n) :=
      {p | A.chart.symm p.1 ≠ C.chart.symm p.2}
    let B := A.chart.target ×ˢ C.chart.target
    have hB : IsOpen B := A.chart.open_target.prod C.chart.open_target
    have hF : ContinuousOn (fun p : X n × X n => A.chart.symm p.1) B :=
      A.chart.continuousOn_symm.comp continuous_fst.continuousOn (fun _ hy => hy.1)
    have hG' : ContinuousOn (fun p : X n × X n => C.chart.symm p.2) B :=
      C.chart.continuousOn_symm.comp continuous_snd.continuousOn (fun _ hy => hy.2)
    have hO : IsOpen (B ∩ O) := by
      let d : X n × X n → M × M := fun p => (A.chart.symm p.1, C.chart.symm p.2)
      exact (hF.prodMk hG').isOpen_inter_preimage hB isClosed_diagonal.isOpen_compl
    obtain ⟨U,V,hU,hxU,hV,hzV,hUV⟩ := mem_nhds_prod_iff'.mp (hO.mem_nhds ⟨⟨hx,hz⟩,hNe⟩)
    have hUA : U ⊆ A.chart.target := fun y hy => (hUV (show (y,z) ∈ U ×ˢ V from ⟨hy,hzV⟩)).1.1
    have hVC : V ⊆ C.chart.target := fun y hy => (hUV (show (x,y) ∈ U ×ˢ V from ⟨hxU,hy⟩)).1.2
    have hDis (y : X n) (hy : y ∈ U) (s : X n) (hs : s ∈ V) :
        A.chart.symm y ≠ C.chart.symm s := (hUV (show (y,s) ∈ U ×ˢ V from ⟨hy,hs⟩)).2
    obtain ⟨A',hA's,hA't,hA'i,hA'm⟩ := restrict_interiorMetricChart A hU hUA
    have hH (s : X n) (hs : s ∈ V) : Harmonic U A.metric (fun y => G (A.chart.symm y, C.chart.symm s)) := by
      have hSin : C.chart.symm s ∈ (J).interior M := C.source_interior (C.chart.map_target (hVC hs))
      have hSout : C.chart.symm s ∉ A'.chart.source := by
        intro hS
        have hST : A'.chart (C.chart.symm s) ∈ U := hA't ▸ A'.chart.map_source hS
        apply hDis _ hST s hs
        rw [← hA'i, A'.chart.left_inv hS]
      have h := harmonic_greenSection_off_pole A' (fun v _ => tsupport_nativeLaplace_subset g v) hG hSin hSout
      rw [hA't,hA'm] at h
      simpa only [hA'i] using h
    refine ⟨U,hU,hxU,hUA,?_⟩
    exact harmonic_parameterSecondOrder hU hV ⟨fun i j => (A.smooth_metric.1 i j).mono hUA,
      fun y hy => A.smooth_metric.2 y (hUA hy)⟩
      (contDiffOn_jointGreen_of_disjoint_charts hG A C hUA hVC hDis)
      hH hzV a b c
  refine ⟨fun x hx => ?_,fun x hx => ?_⟩
  · obtain ⟨U,hU,hxU,_,hH⟩ := hLocal x hx
    exact (hH.1.contDiffAt (hU.mem_nhds hxU)).contDiffWithinAt
  · exact (hLocal x hx).choose_spec.2.2.2.2 x (hLocal x hx).choose_spec.2.1

end CalderonPatch
