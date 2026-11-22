module

public import Proof.CalderonPatch.Energy
public import Proof.CalderonPatch.MatchingDomains
public import Proof.CalderonN.GreenRestriction

import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (MetricField X metricPair InteriorMetricChart)

variable {n : ℕ} [NeZero n] {M₁ M₂ F : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

/-- The coordinate metric is the pullback along the inverse chart. -/
def RealizesCoordinateMetric {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) 1 M] (g : SmoothMetric n M) (e : OpenPartialHomeomorph M (X n))
    (γ : MetricField n) : Prop :=
  ∀ x ∈ e.target, ∀ v w : X n,
    metricPair γ x v w = g.inner (e.symm x)
      (mfderiv 𝓘(ℝ, X n) (𝓡∂ n) e.symm x v) (mfderiv 𝓘(ℝ, X n) (𝓡∂ n) e.symm x w)

/-- A smooth local identification transporting the actual tangent metric. -/
structure IsLocalMetricIsometry (g₁ : SmoothMetric n M₁) (g₂ : SmoothMetric n M₂)
    (e : OpenPartialHomeomorph M₂ M₁) : Prop where
  smooth : ContMDiffOn (𝓡∂ n) (𝓡∂ n) ∞ e e.source
  smooth_inverse : ContMDiffOn (𝓡∂ n) (𝓡∂ n) ∞ e.symm e.target
  metric_eq : ∀ p ∈ e.source, ∀ v w : TangentSpace (𝓡∂ n) p,
    g₂.inner p v w = g₁.inner (e p)
      (mfderiv (𝓡∂ n) (𝓡∂ n) e p v) (mfderiv (𝓡∂ n) (𝓡∂ n) e p w)

variable [MeasurableSpace M₁] [MeasurableSpace M₂]

/-- Equal coordinate metrics and equal source evaluations give a local
isometric match using the identity on the common coordinate neighborhood. -/
theorem exists_localMatch_of_chartAgreement
    (I₂ : SourceEvaluations M₂ F) (I₁ : SourceEvaluations M₁ F)
    (hI₁ : I₁.interior = (𝓡∂ n).interior M₁) (hI₂ : I₂.interior = (𝓡∂ n).interior M₂)
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {μ₁ : Measure M₁} {μ₂ : Measure M₂} {L₁ : (M₁ → ℝ) → M₁ → ℝ} {L₂ : (M₂ → ℝ) → M₂ → ℝ}
    (C₁ : InteriorMetricChart (𝓡∂ n) μ₁ L₁) (C₂ : InteriorMetricChart (𝓡∂ n) μ₂ L₂)
    (hReal₁ : RealizesCoordinateMetric g₁ C₁.chart C₁.metric)
    (hReal₂ : RealizesCoordinateMetric g₂ C₂.chart C₂.metric)
    {B : Set (X n)} (hB : IsOpen B) (hB₁ : B ⊆ C₁.chart.target) (hB₂ : B ⊆ C₂.chart.target)
    (hEq : EqOn C₁.metric C₂.metric B)
    (hEval : ∀ x ∈ B, I₂.value (C₂.chart.symm x) = I₁.value (C₁.chart.symm x)) :
    ∃ E : EvaluationMatch I₂ I₁ (IsLocalMetricIsometry g₁ g₂),
      E.chart.source = C₂.chart.source ∩ C₂.chart ⁻¹' B := by
  let S : Set M₂ := C₂.chart.source ∩ C₂.chart ⁻¹' B
  let e := (C₂.chart.trans C₁.chart.symm).restr S
  have hS : IsOpen S := C₂.chart.continuousOn.isOpen_inter_preimage C₂.chart.open_source hB
  have hsrc : e.source = S := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hS, inter_eq_right]
    intro p hp
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hp.1, hB₁ hp.2⟩
  have hforward {p : M₂} (hp : p ∈ e.source) : C₂.chart p ∈ B := by
    rw [hsrc] at hp
    exact hp.2
  have hback {q : M₁} (hq : q ∈ e.target) : C₁.chart q ∈ B := by
    have hx := hforward (e.map_target hq)
    have he : C₁.chart.symm (C₂.chart (e.symm q)) = q := e.right_inv hq
    rw [← he, C₁.chart.right_inv (hB₁ hx)]
    exact hx
  have hsrc₂ : e.source ⊆ C₂.chart.source := by rw [hsrc]; exact inter_subset_left
  have htar₁ : e.target ⊆ C₁.chart.source := by
    intro q hq
    have hx := hforward (e.map_target hq)
    have he : C₁.chart.symm (C₂.chart (e.symm q)) = q := e.right_inv hq
    exact he ▸ C₁.chart.map_target (hB₁ hx)
  have hD₂ : C₂.chart.MDifferentiable (𝓡∂ n) 𝓘(ℝ, X n) :=
    ⟨C₂.smooth.mdifferentiableOn (by simp), C₂.smooth_inverse.mdifferentiableOn (by simp)⟩
  have hD₁ : C₁.chart.MDifferentiable (𝓡∂ n) 𝓘(ℝ, X n) :=
    ⟨C₁.smooth.mdifferentiableOn (by simp), C₁.smooth_inverse.mdifferentiableOn (by simp)⟩
  have hIso : IsLocalMetricIsometry g₁ g₂ e := by
    refine ⟨C₁.smooth_inverse.comp (C₂.smooth.mono hsrc₂) (fun _ hp => hB₁ (hforward hp)),
      C₂.smooth_inverse.comp (C₁.smooth.mono htar₁) (fun _ hq => hB₂ (hback hq)), ?_⟩
    intro p hp v w
    let x := C₂.chart p
    let D := mfderiv (𝓡∂ n) 𝓘(ℝ, X n) C₂.chart p
    let D₂ := mfderiv 𝓘(ℝ, X n) (𝓡∂ n) C₂.chart.symm x
    let D₁ := mfderiv 𝓘(ℝ, X n) (𝓡∂ n) C₁.chart.symm x
    have hx := hforward hp
    have hinv (t : TangentSpace (𝓡∂ n) p) : D₂ (D t) = t :=
      congrArg (fun L : TangentSpace (𝓡∂ n) p →L[ℝ] TangentSpace (𝓡∂ n) p => L t)
        (hD₂.symm_comp_deriv (hsrc₂ hp))
    have hderiv : mfderiv (𝓡∂ n) (𝓡∂ n) e p = D₁.comp D :=
      mfderiv_comp p (hD₁.mdifferentiableAt_symm (hB₁ hx)) (hD₂.mdifferentiableAt (hsrc₂ hp))
    have h₁ := hReal₁ x (hB₁ hx) (D v) (D w)
    have h₂ : metricPair C₂.metric x (D v) (D w) = g₂.inner p v w := by
      calc
        _ = g₂.inner (C₂.chart.symm x) (D₂ (D v)) (D₂ (D w)) :=
          hReal₂ x (hB₂ hx) (D v) (D w)
        _ = g₂.inner (C₂.chart.symm x) v w :=
          congrArg₂ (fun a b : X n => g₂.inner (C₂.chart.symm x) a b) (hinv v) (hinv w)
        _ = _ := congrArg (fun z : M₂ => g₂.inner z v w) (C₂.chart.left_inv (hsrc₂ hp))
    rw [hderiv]
    calc
      g₂.inner p v w = metricPair C₂.metric x (D v) (D w) := h₂.symm
      _ = metricPair C₁.metric x (D v) (D w) := by
        have hγ : C₂.metric x = C₁.metric x := (hEq hx).symm
        simp only [metricPair, hγ]
      _ = _ := h₁
  refine ⟨⟨e, ?_, ?_, ?_, hIso⟩, hsrc⟩
  · rw [hI₂]
    exact hsrc₂.trans C₂.source_interior
  · rw [hI₁]
    exact htar₁.trans C₁.source_interior
  · intro p hp
    have hv := hEval (C₂.chart p) (hforward hp)
    rwa [C₂.chart.left_inv (hsrc₂ hp)] at hv

end CalderonPatch
