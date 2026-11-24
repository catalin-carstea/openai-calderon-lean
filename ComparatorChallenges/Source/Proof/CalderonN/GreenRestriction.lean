module

public import Proof.CalderonN.Chart
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonN

variable {n : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {J : ModelWithCorners ℝ (X n) H}

/-- The coordinate density for Riemannian volume on an interior chart. -/
def chartVolumeMeasure (Ω : Set (X n)) (g : MetricField n) : Measure (X n) :=
  (volume.restrict Ω).withDensity (fun x => ENNReal.ofReal (Real.sqrt (g x).det))

section Kernel

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The global properties of a supplied Dirichlet Green kernel for the inverse of
−L. The weak law is tested against smooth compactly supported interior functions. -/
structure IsDirichletGreenKernel (J : ModelWithCorners ℝ (X n) H) (μ : Measure M)
    (L : (M → ℝ) → M → ℝ) (G : M × M → ℝ) : Prop where
  smooth_off_diagonal : ContMDiffOn (J.prod J) 𝓘(ℝ, ℝ) ∞ G
    {p | p.1 ∈ J.interior M ∧ p.2 ∈ J.interior M ∧ p.1 ≠ p.2}
  symmetric : ∀ p q, p ∈ J.interior M → q ∈ J.interior M → p ≠ q → G (p, q) = G (q, p)
  continuous_off_pole : ∀ q ∈ J.interior M, ContinuousOn (fun p => G (p, q)) ({q}ᶜ)
  zero_on_boundary : ∀ p ∈ J.boundary M, ∀ q ∈ J.interior M, G (p, q) = 0
  integrable : ∀ q ∈ J.interior M, Integrable (fun p => G (p, q)) μ
  weak_inverse : ∀ q ∈ J.interior M, ∀ u : M → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ u →
    HasCompactSupport u → tsupport u ⊆ J.interior M →
    Integrable (fun p => G (p, q) * (-L u p)) μ ∧
      (∫ p, G (p, q) * (-L u p) ∂μ) = u q

/-- The coordinate realization of the metric, volume and differential operator
on one interior chart. -/
structure InteriorMetricChart (J : ModelWithCorners ℝ (X n) H) (μ : Measure M)
    (L : (M → ℝ) → M → ℝ) where
  chart : OpenPartialHomeomorph M (X n)
  source_interior : chart.source ⊆ J.interior M
  smooth : ContMDiffOn J 𝓘(ℝ, X n) ∞ chart chart.source
  smooth_inverse : ContMDiffOn 𝓘(ℝ, X n) J ∞ chart.symm chart.target
  metric : MetricField n
  smooth_metric : SmoothMetric chart.target metric
  volume_eq : (μ.restrict chart.source).map chart = chartVolumeMeasure chart.target metric
  laplace_eq : ∀ u : M → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ u →
    ∀ p ∈ chart.source, L u p = laplace metric (u ∘ chart.symm) (chart p)

end Kernel

end CalderonN
