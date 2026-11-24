module

public import Proof.CalderonPatch.Energy
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.Clopen
public import Proof.CalderonN.GreenRestriction
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import Proof.CalderonN.Coordinates

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (MetricField X metricPair InteriorMetricChart)

variable {n : ℕ} [NeZero n] {M₁ M₂ F : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

/-- A smooth local identification transporting the actual tangent metric. -/
structure IsLocalMetricIsometry (g₁ : SmoothMetric n M₁) (g₂ : SmoothMetric n M₂)
    (e : OpenPartialHomeomorph M₂ M₁) : Prop where
  smooth : ContMDiffOn (𝓡∂ n) (𝓡∂ n) ∞ e e.source
  smooth_inverse : ContMDiffOn (𝓡∂ n) (𝓡∂ n) ∞ e.symm e.target
  metric_eq : ∀ p ∈ e.source, ∀ v w : TangentSpace (𝓡∂ n) p,
    g₂.inner p v w = g₁.inner (e p)
      (mfderiv (𝓡∂ n) (𝓡∂ n) e p v) (mfderiv (𝓡∂ n) (𝓡∂ n) e p w)

variable [MeasurableSpace M₁] [MeasurableSpace M₂]

end CalderonPatch
