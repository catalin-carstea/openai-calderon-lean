module

public import Proof.CalderonN.CheckedLocalExtension
public import Mathlib.Geometry.Manifold.Instances.Real

public section

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology

namespace CalderonN

/-- A smooth mean-zero test in the kernel has zero four-term energy, with the same thresholds
    throughout the family of admitted radii and metrics. -/
theorem zeroEnergyOfZeroOutput {n : ℕ} (hn : 3 ≤ n) (Y Ω : Set (X n)) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hcpt : IsCompact (closure Y)) (hin : closure Y ⊆ Ω) :
    ∃ m : ℕ, ∀ (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ),
      1 ≤ K → 0 < ρ → 0 < c₀ → ∃ floor ε₀ : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧
        ∀ d ε, 0 ≤ ε → ε ≤ ε₀ → Admissible Y Ω K ρ c₀ M Cj floor ε d →
          ∀ φ, Test Y d.γ d.frame φ → traceNorm Y d φ = 0 → energyNorm Y d φ = 0 := by
  obtain ⟨m, hm⟩ := coercivity hn Y Ω hY hΩ hcpt hin
  refine ⟨m, ?_⟩
  intro K ρ c₀ M Cj hK hρ hc₀
  obtain ⟨floor, ε₀, C, hf, hε, _, bound⟩ := hm K ρ c₀ M Cj hK hρ hc₀
  refine ⟨floor, ε₀, hf, hε, ?_⟩
  intro d ε hε₁ hε₂ hd φ hφ hzero
  have h := bound d ε hε₁ hε₂ hd φ hφ
  rw [hzero, mul_zero] at h
  exact le_antisymm h (Real.sqrt_nonneg _)

/-- Downstream chart gluing uses equality in the neighborhood filter at the
contact point. -/
theorem eventuallyEqMetric
    {n : ℕ} (hn : 3 ≤ n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsSmoothSide Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : X n × X n → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {m : ℕ} {u₁ u₂ : Fin m → X n → ℝ}
    (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a)) (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a))
    (hpairs : ∀ a, EqOn (u₁ a) (u₂ a) W) (hspan : HessianSpanning g₁ u₁) :
    g₁ =ᶠ[𝓝 (0 : X n)] g₂ := by
  obtain ⟨r, hr, _, heq⟩ := localMetricExtension hn hΩ hW hWΩ hside
    hg₁ hg₂ hchart₁ hchart₂ hG₁ hG₂ hmetric hgreen hu₁ hu₂ hpairs hspan
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : X n) hr) heq

section ManifoldApplication

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁]
  [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁]
  [TopologicalSpace M₂] [T2Space M₂]
  [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂]

/-- Read the given Dirichlet kernels in the two identified interior harmonic charts. -/
theorem localMetricExtensionFromDirichletKernels
    (hn : 3 ≤ n)
    [CompactSpace M₁] [ConnectedSpace M₁] [IsManifold (𝓡∂ n) ∞ M₁]
    [CompactSpace M₂] [ConnectedSpace M₂] [IsManifold (𝓡∂ n) ∞ M₂]
    (_hb₁ : ((𝓡∂ n).boundary M₁).Nonempty) (_hb₂ : ((𝓡∂ n).boundary M₂).Nonempty)
    {μ₁ : Measure M₁} {μ₂ : Measure M₂}
    {L₁ : (M₁ → ℝ) → M₁ → ℝ} {L₂ : (M₂ → ℝ) → M₂ → ℝ}
    (loc₁ : ∀ v : M₁ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₁ v) ⊆ tsupport v)
    (loc₂ : ∀ v : M₂ → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ v → tsupport (L₂ v) ⊆ tsupport v)
    (C₁ : InteriorMetricChart (𝓡∂ n) μ₁ L₁)
    (C₂ : InteriorMetricChart (𝓡∂ n) μ₂ L₂)
    (hΩ : C₁.chart.target = C₂.chart.target)
    {W : Set (X n)} (hW : IsOpen W) (hWΩ : W ⊆ C₁.chart.target)
    (hside : ContainsSmoothSide C₁.chart.target W)
    (hh₁ : HarmonicCoordinates C₁.chart.target C₁.metric)
    (hh₂ : HarmonicCoordinates C₂.chart.target C₂.metric)
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ}
    (hG₁ : IsDirichletGreenKernel (𝓡∂ n) μ₁ L₁ G₁)
    (hG₂ : IsDirichletGreenKernel (𝓡∂ n) μ₂ L₂ G₂)
    (hmetric : EqOn C₁.metric C₂.metric W)
    (hgreen : ∀ p ∈ OffDiagonal W,
      G₁ (C₁.chart.symm p.1, C₁.chart.symm p.2) =
        G₂ (C₂.chart.symm p.1, C₂.chart.symm p.2))
    {m : ℕ} {u₁ u₂ : Fin m → X n → ℝ}
    (hu₁ : ∀ a, Harmonic C₁.chart.target C₁.metric (u₁ a))
    (hu₂ : ∀ a, Harmonic C₂.chart.target C₂.metric (u₂ a))
    (hpairs : ∀ a, EqOn (u₁ a) (u₂ a) W) (hspan : HessianSpanning C₁.metric u₁) :
    ∃ r > 0, Metric.ball (0 : X n) r ⊆ C₁.chart.target ∧
      EqOn C₁.metric C₂.metric (Metric.ball 0 r) := by
  have h₁ := GreenGerm.of_dirichletKernel C₁ loc₁ hG₁
  have h₂ := GreenGerm.of_dirichletKernel C₂ loc₂ hG₂
  exact localMetricExtension hn C₁.chart.open_target hW hWΩ hside
    C₁.smooth_metric (hΩ.symm ▸ C₂.smooth_metric) hh₁ (hΩ.symm ▸ hh₂)
    h₁ (hΩ.symm ▸ h₂) hmetric hgreen hu₁ (hΩ.symm ▸ hu₂) hpairs hspan


end ManifoldApplication

end CalderonN
