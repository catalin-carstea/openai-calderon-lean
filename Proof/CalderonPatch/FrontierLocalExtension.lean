module

public import Proof.CalderonN.GreenRestriction
public import Proof.CalderonPatch.TouchingBall
public import Mathlib.Geometry.Manifold.Instances.Real

import Proof.CalderonN.CheckedLocalExtension
import Proof.CalderonPatch.ChartTranslation
import Mathlib.Tactic

@[expose] public section

open MeasureTheory Metric Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN

variable {n : ℕ} [NeZero n]

/-- The symmetric harmonic Hessian hyperplane at the contact point. -/
def HessianSpanningAt {m : ℕ} (g : MetricField n) (u : Fin m → X n → ℝ) (q : X n) : Prop :=
  ∀ H : Mat n, H ∈ Submodule.span ℝ (range fun a => hessian (u a) q) ↔
    H.transpose = H ∧ ((g q)⁻¹ * H).trace = 0

/-- Apply the checked local metric extension at a point where an open ball
in the matched coordinate region touches its frontier. -/
theorem localMetricExtension_at_touchingBall (hn : 3 ≤ n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    {q c : X n} {r : ℝ} (hq : q ∈ Ω) (hr : 0 < r) (hcontact : dist q c = r)
    (hball : ball c r ⊆ W)
    {g₁ g₂ : MetricField n} (hg₁ : CalderonN.SmoothMetric Ω g₁)
    (hg₂ : CalderonN.SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : X n × X n → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {m : ℕ} {u₁ u₂ : Fin m → X n → ℝ} (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a))
    (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a)) (hpairs : ∀ a, EqOn (u₁ a) (u₂ a) W)
    (hspan : HessianSpanningAt g₁ u₁ q) :
    ∃ ρ > 0, ball q ρ ⊆ Ω ∧ EqOn g₁ g₂ (ball q ρ) := by
  let T : Set (X n) := (q + ·) ⁻¹' Ω
  let S : Set (X n) := (q + ·) ⁻¹' W
  let g₁' (x : X n) := g₁ (q + x)
  let u₁' (a : Fin m) (x : X n) := u₁ a (q + x)
  have hT : IsOpen T := hΩ.preimage (continuous_const.add continuous_id)
  have hS : IsOpen S := hW.preimage (continuous_const.add continuous_id)
  have h₀ : (0 : X n) ∈ T := by simpa only [T, mem_preimage, add_zero] using hq
  have hc : ‖c - q‖ = r := by rw [← dist_eq_norm, dist_comm, hcontact]
  have hball' : ball (c - q) r ⊆ S := by
    intro x hx
    apply hball
    rw [mem_ball, dist_eq_norm] at hx ⊢
    rwa [show q + x - c = x - (c - q) by abel]
  have hside := containsSmoothSide_of_ball hT h₀ hr hc hball'
  have hg' : EqOn (fun p : X n × X n => G₁ (q + p.1, q + p.2))
      (fun p => G₂ (q + p.1, q + p.2)) (OffDiagonal S) :=
    fun _ hp => hgreen ⟨hp.1, hp.2.1, fun h => hp.2.2 (add_left_cancel h)⟩
  have hspan' : HessianSpanning g₁' u₁' := by
    simpa only [HessianSpanning, HessianSpanningAt, g₁', u₁', hessian_translate, add_zero] using hspan
  obtain ⟨ρ, hρ, hρT, hEq⟩ := CalderonN.localMetricExtension hn hT hS
    (fun _ hx => hWΩ hx) hside
    (smoothMetric_translate hg₁ q) (smoothMetric_translate hg₂ q)
    (harmonicCoordinates_translate hΩ hchart₁ q) (harmonicCoordinates_translate hΩ hchart₂ q)
    (greenGerm_translate hΩ hG₁ q) (greenGerm_translate hΩ hG₂ q)
    (fun _ hx => hmetric hx) hg'
    (fun a => harmonic_translate (hu₁ a) q) (fun a => harmonic_translate (hu₂ a) q)
    (fun a _ hx => hpairs a hx) hspan'
  have hshift {x : X n} (hx : x ∈ ball q ρ) : x - q ∈ ball (0 : X n) ρ := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hx
  have hcancel (x : X n) : q + (x - q) = x := by abel
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro x hx
    have ht : q + (x - q) ∈ Ω := hρT (hshift hx)
    simpa only [hcancel] using ht
  · intro x hx
    have he : g₁ (q + (x - q)) = g₂ (q + (x - q)) := hEq (hshift hx)
    simpa only [hcancel] using he

section DirichletKernels

variable {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁]
  [TopologicalSpace M₂] [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂]

/-- Use both supplied ambient Dirichlet kernels at the contact, with their
original densities and the harmonic chart coordinate operators. -/
theorem localMetricExtension_at_touchingBall_of_dirichletKernels (hn : 3 ≤ n)
    {μ₁ : Measure M₁} {μ₂ : Measure M₂}
    {L₁ : (M₁ → ℝ) → M₁ → ℝ} {L₂ : (M₂ → ℝ) → M₂ → ℝ}
    (loc₁ : ∀ v : M₁ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₁ v) ⊆ tsupport v)
    (loc₂ : ∀ v : M₂ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₂ v) ⊆ tsupport v)
    (C₁ : InteriorMetricChart (𝓡∂ n) μ₁ L₁) (C₂ : InteriorMetricChart (𝓡∂ n) μ₂ L₂)
    (hΩ : C₁.chart.target = C₂.chart.target)
    {W : Set (X n)} (hW : IsOpen W) (hWΩ : W ⊆ C₁.chart.target)
    {q c : X n} {r : ℝ} (hq : q ∈ C₁.chart.target) (hr : 0 < r) (hcontact : dist q c = r)
    (hball : ball c r ⊆ W)
    (hchart₁ : HarmonicCoordinates C₁.chart.target C₁.metric)
    (hchart₂ : HarmonicCoordinates C₂.chart.target C₂.metric)
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ}
    (hG₁ : IsDirichletGreenKernel (𝓡∂ n) μ₁ L₁ G₁)
    (hG₂ : IsDirichletGreenKernel (𝓡∂ n) μ₂ L₂ G₂)
    (hmetric : EqOn C₁.metric C₂.metric W)
    (hgreen : ∀ p ∈ OffDiagonal W, G₁ (C₁.chart.symm p.1, C₁.chart.symm p.2) =
      G₂ (C₂.chart.symm p.1, C₂.chart.symm p.2))
    {m : ℕ} {u₁ u₂ : Fin m → X n → ℝ} (hu₁ : ∀ a, Harmonic C₁.chart.target C₁.metric (u₁ a))
    (hu₂ : ∀ a, Harmonic C₂.chart.target C₂.metric (u₂ a))
    (hpairs : ∀ a, EqOn (u₁ a) (u₂ a) W) (hspan : HessianSpanningAt C₁.metric u₁ q) :
    ∃ ρ > 0, ball q ρ ⊆ C₁.chart.target ∧ EqOn C₁.metric C₂.metric (ball q ρ) := by
  exact localMetricExtension_at_touchingBall hn C₁.chart.open_target hW hWΩ hq hr hcontact hball
    C₁.smooth_metric (hΩ.symm ▸ C₂.smooth_metric) hchart₁ (hΩ.symm ▸ hchart₂)
    (GreenGerm.of_dirichletKernel C₁ loc₁ hG₁) (hΩ.symm ▸ GreenGerm.of_dirichletKernel C₂ loc₂ hG₂)
    hmetric hgreen hu₁ (hΩ.symm ▸ hu₂) hpairs hspan

end DirichletKernels

end CalderonPatch
