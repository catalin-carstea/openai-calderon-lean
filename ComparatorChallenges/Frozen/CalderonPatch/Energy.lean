module

public import ComparatorChallenges.Frozen.CalderonN.Coordinates
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (axis Mat MetricField X)

variable {n : ℕ} [NeZero n] {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]

/-- A smooth positive definite metric on the tangent bundle of a manifold with boundary. -/
abbrev SmoothMetric (n : ℕ) [NeZero n] (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M] :=
  Bundle.ContMDiffRiemannianMetric (𝓡∂ n) ∞ (X n)
    (fun x : M => TangentSpace (𝓡∂ n) x)

/-- Metric coefficients in the canonical extended coordinate chart.
The derivative is taken within the model half space, including at boundary points. -/
def chartMetric (g : SmoothMetric n M) (p : M) : MetricField n :=
  fun y i j =>
    let e := extChartAt (𝓡∂ n) p
    let D := mfderivWithin 𝓘(ℝ, X n) (𝓡∂ n) e.symm (range (𝓡∂ n)) y
    g.inner (e.symm y) (D (axis i)) (D (axis j))

variable [MeasurableSpace M]

/-- The positive Riemannian density relative to orthonormal Euclidean coordinates. -/
def IsMetricVolume (g : SmoothMetric n M) (μ : Measure M) : Prop :=
  ∀ p : M,
    let e := extChartAt (𝓡∂ n) p
    (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity
        (fun y => ENNReal.ofReal (Real.sqrt ((chartMetric g p y).det)))

/-- Squared dual norm, expressed by the supremum of the metric quadratic polynomial. -/
def covectorEnergy (g : SmoothMetric n M) (x : M)
    (a : TangentSpace (𝓡∂ n) x →L[ℝ] ℝ) : ℝ :=
  sSup (range fun v => 2 * a v - g.inner x v v)

/-- The variational quadratic Dirichlet energy on the smooth trace class. -/
def dirichletQuadraticEnergy (g : SmoothMetric n M) (μ : Measure M) (f : M → ℝ) : ℝ :=
  sInf { c : ℝ | ∃ u : M → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ u ∧
    EqOn u f ((𝓡∂ n).boundary M) ∧
    c = ∫ x, covectorEnergy g x (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) u x) ∂μ }

/-- Equality of the quadratic energy for smooth traces supported in the measured patch. -/
def PatchEnergyEqual (g₁ g₂ : SmoothMetric n M) (μ₁ μ₂ : Measure M)
    (Γ : Set ((𝓡∂ n).boundary M)) : Prop :=
  ∀ f : M → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f →
    tsupport (fun p : (𝓡∂ n).boundary M => f p) ⊆ Γ →
    dirichletQuadraticEnergy g₁ μ₁ f = dirichletQuadraticEnergy g₂ μ₂ f

/-- A map which fixes the measured subset of the original boundary. -/
def FixesPatch (Γ : Set ((𝓡∂ n).boundary M)) (Φ : M → M) : Prop :=
  ∀ p : (𝓡∂ n).boundary M, p ∈ Γ → Φ p = (p : M)

/-- The second metric is the pullback of the first, as tangent bilinear forms. -/
def PullbackMetric (g₁ g₂ : SmoothMetric n M) (Φ : M → M) : Prop :=
  ∀ (x : M) (v w : TangentSpace (𝓡∂ n) x),
    g₂.inner x v w =
      g₁.inner (Φ x) (mfderiv (𝓡∂ n) (𝓡∂ n) Φ x v) (mfderiv (𝓡∂ n) (𝓡∂ n) Φ x w)

end CalderonPatch
