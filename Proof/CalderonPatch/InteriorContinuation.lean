module

public import Proof.CalderonPatch.FrontierCharts
public import Proof.CalderonPatch.MaximalMatch

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (IsDirichletGreenKernel)

variable {n : ℕ} [NeZero n] {F M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]
  [CompactSpace M₂] [LocallyConnectedSpace M₂]

/-- The interior continuation step, conditional on the production of
paired harmonic charts at each frontier of the seeded matching component. -/
theorem exists_globalInteriorIsometry (hn : 3 ≤ n)
    (I₂ : SourceEvaluations M₂ F) (I₁ : SourceEvaluations M₁ F)
    (hI₁ : I₁.interior = (𝓡∂ n).interior M₁) (hI₂ : I₂.interior = (𝓡∂ n).interior M₂)
    (hConn₁ : IsConnected I₁.interior) (hConn₂ : IsConnected I₂.interior)
    (g₁ : SmoothMetric n M₁) (g₂ : SmoothMetric n M₂)
    {μ₁ : Measure M₁} {μ₂ : Measure M₂} {L₁ : (M₁ → ℝ) → M₁ → ℝ} {L₂ : (M₂ → ℝ) → M₂ → ℝ}
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ}
    (loc₁ : ∀ v : M₁ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₁ v) ⊆ tsupport v)
    (loc₂ : ∀ v : M₂ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₂ v) ⊆ tsupport v)
    (hG₁ : IsDirichletGreenKernel (𝓡∂ n) μ₁ L₁ G₁)
    (hG₂ : IsDirichletGreenKernel (𝓡∂ n) μ₂ L₂ G₂)
    {seed : M₂} (hseed : seed ∈ matchingDomain I₂ I₁ (IsLocalMetricIsometry g₁ g₂))
    (hCharts :
      let W := connectedComponentIn (matchingDomain I₂ I₁ (IsLocalMetricIsometry g₁ g₂)) seed
      ∀ p ∈ I₂.interior, p ∈ closure W → p ∉ W →
        Nonempty (FrontierCharts I₂ I₁ g₁ g₂ μ₁ μ₂ L₁ L₂ G₁ G₂ W p)) :
    ∃ e : OpenPartialHomeomorph M₂ M₁,
      e.source = I₂.interior ∧ e.target = I₁.interior ∧ IsLocalMetricIsometry g₁ g₂ e ∧
      (∀ p ∈ e.source, I₂.value p = I₁.value (e p)) ∧
      ∀ E : EvaluationMatch I₂ I₁ (IsLocalMetricIsometry g₁ g₂), EqOn e E.chart E.chart.source := by
  let P := IsLocalMetricIsometry g₁ g₂
  let D := matchingDomain I₂ I₁ P
  let W := connectedComponentIn D seed
  have hW : IsOpen W := (matchingDomain_isOpen I₂ I₁ P).connectedComponentIn
  have hSourceOpen : IsOpen I₂.interior := by
    rw [hI₂]
    exact (𝓡∂ n).isOpen_interior (n := ∞) (by simp)
  obtain ⟨e, hsource, htarget, hEval, hCover, hAgree⟩ :=
    exists_interiorEvaluationHomeomorph I₂ I₁ P hSourceOpen hConn₂ hConn₁ hseed
      (fun p hp hcl hout =>
        (hCharts p hp hcl hout).elim fun C => C.exists_match_beyond hI₁ hI₂ hn hW hcl hout loc₁ loc₂ hG₁ hG₂)
  have hsub (E : EvaluationMatch I₂ I₁ P) : E.chart.source ⊆ e.source := hsource ▸ E.source_interior
  have hInvAgree (E : EvaluationMatch I₂ I₁ P) : EqOn e.symm E.chart.symm E.chart.target := by
    intro q hq
    have hx := E.chart.map_target hq
    have he : e (E.chart.symm q) = q := (hAgree E hx).trans (E.chart.right_inv hq)
    exact (congrArg e.symm he.symm).trans (e.left_inv (hsub E hx))
  refine ⟨e, hsource, htarget, ⟨?_, ?_, ?_⟩, hEval, hAgree⟩
  · intro p hp
    obtain ⟨E, hpE⟩ := hCover p hp
    have hEq : (e : M₂ → M₁) =ᶠ[𝓝 p] E.chart :=
      Filter.mem_of_superset (E.chart.open_source.mem_nhds hpE) (fun _ hx => hAgree E hx)
    exact ((E.property.smooth.contMDiffAt (E.chart.open_source.mem_nhds hpE)).congr_of_eventuallyEq
      hEq).contMDiffWithinAt
  · intro q hq
    obtain ⟨E, hpE⟩ := hCover (e.symm q) (e.map_target hq)
    have hqE := E.chart.map_source hpE
    rw [← hAgree E hpE, e.right_inv hq] at hqE
    have hEq : (e.symm : M₁ → M₂) =ᶠ[𝓝 q] E.chart.symm :=
      Filter.mem_of_superset (E.chart.open_target.mem_nhds hqE) (fun _ hx => hInvAgree E hx)
    exact ((E.property.smooth_inverse.contMDiffAt (E.chart.open_target.mem_nhds hqE)).congr_of_eventuallyEq
      hEq).contMDiffWithinAt
  · intro p hp v w
    obtain ⟨E, hpE⟩ := hCover p hp
    have hEq : (e : M₂ → M₁) =ᶠ[𝓝 p] E.chart :=
      Filter.mem_of_superset (E.chart.open_source.mem_nhds hpE) (fun _ hx => hAgree E hx)
    have hD (t : CalderonN.X n) : (mfderiv (𝓡∂ n) (𝓡∂ n) e p t : CalderonN.X n) =
        mfderiv (𝓡∂ n) (𝓡∂ n) E.chart p t :=
      congrArg (fun L : CalderonN.X n →L[ℝ] CalderonN.X n => L t)
        (hEq.mfderiv_eq (I := 𝓡∂ n) (I' := 𝓡∂ n))
    let D := mfderiv (𝓡∂ n) (𝓡∂ n) E.chart p
    calc
      _ = g₁.inner (E.chart p) (D v) (D w) := E.property.metric_eq p hpE v w
      _ = g₁.inner (e p) (D v) (D w) :=
        congrArg (fun y : M₁ => g₁.inner y (D v) (D w)) (hAgree E hpE).symm
      _ = _ := congrArg₂ (fun a b : CalderonN.X n => g₁.inner (e p) a b) (hD v).symm (hD w).symm

end CalderonPatch
