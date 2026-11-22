module

public import Proof.CalderonPatch.FrontierContinuation
public import Proof.CalderonPatch.MatchedCoordinates

import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (Harmonic HarmonicCoordinates InteriorMetricChart IsDirichletGreenKernel OffDiagonal X)

variable {n : ℕ} {M₂ : Type*} [TopologicalSpace M₂]

/-- The part of a coordinate target already identified by the match. -/
def matchedImage (e : OpenPartialHomeomorph M₂ (X n)) (W : Set M₂) : Set (X n) :=
  e '' (W ∩ e.source)

theorem mem_matchedImage {e : OpenPartialHomeomorph M₂ (X n)} {W : Set M₂} {x : X n} :
    x ∈ matchedImage e W ↔ x ∈ e.target ∧ e.symm x ∈ W := by
  constructor
  · rintro ⟨p, ⟨hpW, hp⟩, rfl⟩
    exact ⟨e.map_source hp, (e.left_inv hp).symm ▸ hpW⟩
  · rintro ⟨hx, hxW⟩
    exact ⟨e.symm x, ⟨hxW, e.map_target hx⟩, e.right_inv hx⟩

variable [NeZero n] {F M₁ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

/-- The actual chart data required at a frontier point of the matching set.
The same evaluated source functions are used for coordinates, Hessians
and extension of the match. -/
structure FrontierCharts
    (I₂ : SourceEvaluations M₂ F) (I₁ : SourceEvaluations M₁ F)
    (g₁ : SmoothMetric n M₁) (g₂ : SmoothMetric n M₂)
    (μ₁ : Measure M₁) (μ₂ : Measure M₂)
    (L₁ : (M₁ → ℝ) → M₁ → ℝ) (L₂ : (M₂ → ℝ) → M₂ → ℝ)
    (G₁ : M₁ × M₁ → ℝ) (G₂ : M₂ × M₂ → ℝ) (W : Set M₂) (p : M₂) where
  first : InteriorMetricChart (𝓡∂ n) μ₁ L₁
  second : InteriorMetricChart (𝓡∂ n) μ₂ L₂
  target_eq : first.chart.target = second.chart.target
  point_in_source : p ∈ second.chart.source
  first_realizes : RealizesCoordinateMetric g₁ first.chart first.metric
  second_realizes : RealizesCoordinateMetric g₂ second.chart second.metric
  first_harmonic_coord : HarmonicCoordinates first.chart.target first.metric
  second_harmonic_coord : HarmonicCoordinates second.chart.target second.metric
  first_sources : ∀ a, Harmonic first.chart.target first.metric (fun x => I₁.value (first.chart.symm x) a)
  second_sources : ∀ a, Harmonic second.chart.target second.metric (fun x => I₂.value (second.chart.symm x) a)
  metric_eq : EqOn first.metric second.metric (matchedImage second.chart W)
  green_eq : ∀ q ∈ OffDiagonal (matchedImage second.chart W),
    G₁ (first.chart.symm q.1, first.chart.symm q.2) =
      G₂ (second.chart.symm q.1, second.chart.symm q.2)
  evaluations_eq : ∀ x ∈ matchedImage second.chart W,
    I₁.value (first.chart.symm x) = I₂.value (second.chart.symm x)
  count : ℕ
  sources : Fin count → F
  spans : ∀ x ∈ first.chart.target,
    HessianSpanningAt first.metric (fun a z => I₁.value (first.chart.symm z) (sources a)) x

/-- From paired harmonic charts and the actual extended kernels, construct
a connected local isometry that matches all evaluations and crosses the
old frontier. -/
theorem FrontierCharts.exists_match_beyond
    {I₂ : SourceEvaluations M₂ F} {I₁ : SourceEvaluations M₁ F}
    (hI₁ : I₁.interior = (𝓡∂ n).interior M₁) (hI₂ : I₂.interior = (𝓡∂ n).interior M₂)
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {μ₁ : Measure M₁} {μ₂ : Measure M₂} {L₁ : (M₁ → ℝ) → M₁ → ℝ} {L₂ : (M₂ → ℝ) → M₂ → ℝ}
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ} {W : Set M₂} {p : M₂}
    (C : FrontierCharts I₂ I₁ g₁ g₂ μ₁ μ₂ L₁ L₂ G₁ G₂ W p)
    (hn : 3 ≤ n) (hW : IsOpen W) (hpcl : p ∈ closure W) (hpW : p ∉ W)
    (loc₁ : ∀ v : M₁ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₁ v) ⊆ tsupport v)
    (loc₂ : ∀ v : M₂ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₂ v) ⊆ tsupport v)
    (hG₁ : IsDirichletGreenKernel (𝓡∂ n) μ₁ L₁ G₁)
    (hG₂ : IsDirichletGreenKernel (𝓡∂ n) μ₂ L₂ G₂) :
    ∃ E : EvaluationMatch I₂ I₁ (IsLocalMetricIsometry g₁ g₂),
      IsPreconnected E.chart.source ∧ (E.chart.source ∩ W).Nonempty ∧
      ∃ q ∈ E.chart.source, q ∉ W := by
  let e := C.second.chart
  let A := matchedImage e W
  have hA : IsOpen A := e.isOpen_image_of_subset_source (hW.inter e.open_source) inter_subset_right
  have hAΩ : A ⊆ C.first.chart.target := fun _ hx => C.target_eq ▸ (mem_matchedImage.mp hx).1
  have hp : p ∈ e.source := C.point_in_source
  have hzΩ : e p ∈ C.first.chart.target := C.target_eq ▸ e.map_source hp
  have hcl : p ∈ closure (W ∩ e.source) := by
    rw [mem_closure_iff_frequently] at hpcl ⊢
    exact hpcl.and_eventually (e.open_source.mem_nhds hp)
  have hzcl : e p ∈ closure A :=
    mem_closure_image (e.continuousOn.continuousAt (e.open_source.mem_nhds hp)) hcl
  have hzA : e p ∉ A := by
    intro hz
    exact hpW (e.left_inv hp ▸ (mem_matchedImage.mp hz).2)
  obtain ⟨q, ρ, hq, hρ, hB₁, hmeet, hEq, hpairs⟩ :=
    exists_frontierExtension_of_dirichletKernels hn loc₁ loc₂ C.first C.second C.target_eq
      hA hAΩ hzΩ hzcl hzA C.first_harmonic_coord C.second_harmonic_coord hG₁ hG₂ C.metric_eq C.green_eq
      (fun a x => I₁.value x a) (fun a x => I₂.value x a) C.first_sources C.second_sources
      (fun a _ hx => congrFun (C.evaluations_eq _ hx) a) C.sources C.spans
  have hB₂ : ball q ρ ⊆ e.target := C.target_eq ▸ hB₁
  obtain ⟨E, hsrc⟩ := exists_localMatch_of_chartAgreement I₂ I₁ hI₁ hI₂ C.first C.second
    C.first_realizes C.second_realizes isOpen_ball hB₁ hB₂ hEq
    (fun _ hx => funext fun a => (hpairs a hx).symm)
  have himg : E.chart.source = e.symm '' ball q ρ := by
    rw [hsrc]
    ext y
    constructor
    · exact fun hy => ⟨e y, hy.2, e.left_inv hy.1⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e.map_target (hB₂ hx), ?_⟩
      change e (e.symm x) ∈ ball q ρ
      rwa [e.right_inv (hB₂ hx)]
  refine ⟨E, ?_, ?_, ?_⟩
  · rw [himg]
    exact (Metric.isConnected_ball hρ).2.image e.symm (e.continuousOn_symm.mono hB₂)
  · obtain ⟨b, hb, hbA⟩ := hmeet
    exact ⟨e.symm b, himg ▸ mem_image_of_mem e.symm hb, (mem_matchedImage.mp hbA).2⟩
  · have hqB : q ∈ ball q ρ := mem_ball_self hρ
    refine ⟨e.symm q, himg ▸ mem_image_of_mem e.symm hqB, fun h => ?_⟩
    exact hq (mem_matchedImage.mpr ⟨hB₂ hqB, h⟩)

end CalderonPatch
