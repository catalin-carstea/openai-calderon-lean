module

public import Proof.CalderonPatch.FrontierLocalExtension

import Proof.CalderonN.ChartUniqueContinuation
import Proof.CalderonN.GreenWeak
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Real

public section

open MeasureTheory Metric Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN

variable {n : ℕ} [NeZero n] {F M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁]
  [TopologicalSpace M₂] [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂]

/-- Extend a matched coordinate neighborhood beyond its frontier. The finite
Hessian family is chosen from the same source solutions transported on the
whole matching domain. The Green kernels keep their original normalization. -/
theorem exists_frontierExtension_of_dirichletKernels (hn : 3 ≤ n)
    {μ₁ : Measure M₁} {μ₂ : Measure M₂}
    {L₁ : (M₁ → ℝ) → M₁ → ℝ} {L₂ : (M₂ → ℝ) → M₂ → ℝ}
    (loc₁ : ∀ v : M₁ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₁ v) ⊆ tsupport v)
    (loc₂ : ∀ v : M₂ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₂ v) ⊆ tsupport v)
    (C₁ : InteriorMetricChart (𝓡∂ n) μ₁ L₁) (C₂ : InteriorMetricChart (𝓡∂ n) μ₂ L₂)
    (hΩ : C₁.chart.target = C₂.chart.target)
    {W : Set (X n)} (hW : IsOpen W) (hWΩ : W ⊆ C₁.chart.target)
    {z : X n} (hzΩ : z ∈ C₁.chart.target) (hzcl : z ∈ closure W) (hzW : z ∉ W)
    (hchart₁ : HarmonicCoordinates C₁.chart.target C₁.metric)
    (hchart₂ : HarmonicCoordinates C₂.chart.target C₂.metric)
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ}
    (hG₁ : IsDirichletGreenKernel (𝓡∂ n) μ₁ L₁ G₁)
    (hG₂ : IsDirichletGreenKernel (𝓡∂ n) μ₂ L₂ G₂)
    (hmetric : EqOn C₁.metric C₂.metric W)
    (hgreen : ∀ p ∈ OffDiagonal W, G₁ (C₁.chart.symm p.1, C₁.chart.symm p.2) =
      G₂ (C₂.chart.symm p.1, C₂.chart.symm p.2))
    (v₁ : F → M₁ → ℝ) (v₂ : F → M₂ → ℝ)
    (hv₁ : ∀ a, Harmonic C₁.chart.target C₁.metric (v₁ a ∘ C₁.chart.symm))
    (hv₂ : ∀ a, Harmonic C₂.chart.target C₂.metric (v₂ a ∘ C₂.chart.symm))
    (hpairs : ∀ a, EqOn (v₁ a ∘ C₁.chart.symm) (v₂ a ∘ C₂.chart.symm) W)
    {m : ℕ} (chooseSource : Fin m → F)
    (hspan : ∀ q ∈ C₁.chart.target,
      HessianSpanningAt C₁.metric (fun a => v₁ (chooseSource a) ∘ C₁.chart.symm) q) :
    ∃ (q : X n) (ρ : ℝ), q ∉ W ∧ 0 < ρ ∧ ball q ρ ⊆ C₁.chart.target ∧
      (ball q ρ ∩ W).Nonempty ∧ EqOn C₁.metric C₂.metric (ball q ρ) ∧
      ∀ a, EqOn (v₁ a ∘ C₁.chart.symm) (v₂ a ∘ C₂.chart.symm) (ball q ρ) := by
  obtain ⟨c, r, q, _, hr, hq, hqW, hcontact, _, hball⟩ :=
    exists_touchingBall C₁.chart.open_target hW hzΩ hzcl hzW
  obtain ⟨ρ, hρ, hρΩ, hEq⟩ := localMetricExtension_at_touchingBall_of_dirichletKernels
    hn loc₁ loc₂ C₁ C₂ hΩ hW hWΩ hq hr hcontact hball hchart₁ hchart₂ hG₁ hG₂ hmetric hgreen
    (fun a => hv₁ (chooseSource a)) (fun a => hv₂ (chooseSource a))
    (fun a => hpairs (chooseSource a)) (hspan q hq)
  have hqcl : q ∈ closure W := closure_mono hball (by
    rw [closure_ball c hr.ne']
    exact hcontact.le)
  obtain ⟨x, hxW, hx⟩ := Metric.mem_closure_iff.mp hqcl ρ hρ
  have hmeet : (ball q ρ ∩ W).Nonempty := ⟨x, by simpa only [mem_ball, dist_comm x q] using hx, hxW⟩
  refine ⟨q, ρ, hqW, hρ, hρΩ, hmeet, hEq, ?_⟩
  intro a
  have h₁ : Harmonic (ball q ρ) C₁.metric (v₁ a ∘ C₁.chart.symm) :=
    ⟨(hv₁ a).1.mono hρΩ, fun x hx => (hv₁ a).2 x (hρΩ hx)⟩
  have hρΩ₂ : ball q ρ ⊆ C₂.chart.target := hΩ ▸ hρΩ
  have h₂ : Harmonic (ball q ρ) C₁.metric (v₂ a ∘ C₂.chart.symm) :=
    ⟨(hv₂ a).1.mono hρΩ₂, fun x hx =>
      (laplace_congrOn isOpen_ball hEq (fun _ _ => rfl) hx).trans ((hv₂ a).2 x (hρΩ₂ hx))⟩
  exact harmonic_eqOn_of_eqOn_open isOpen_ball (Metric.isConnected_ball hρ)
    (isOpen_ball.inter hW) hmeet inter_subset_left
    ⟨fun i j => (C₁.smooth_metric.1 i j).mono hρΩ, fun x hx => C₁.smooth_metric.2 x (hρΩ hx)⟩
    h₁ h₂ (fun _ hx => hpairs a hx.2)

end CalderonPatch
