module

public import Proof.CalderonPatch.NativeNormalChart
import Proof.CalderonN.MetricPullback
import Mathlib.Tactic.Ring
public import Proof.CalderonPatch.BoundaryNormalLaplacian
public import Proof.CalderonN.Chart
public import Proof.CalderonN.Coordinates
public import Proof.CalderonPatch.Energy

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField metricPair pullbackMetric)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

@[expose] def inwardHalfSpace (n : ℕ) [NeZero n] : Set (X n) := {x | 0 ≤ x (0 : I n)}

@[expose] def positiveHalfSpace (n : ℕ) [NeZero n] : Set (X n) := {x | 0 < x (0 : I n)}

/-- An actual boundary normal chart, with the signed normalized
metric in the orthonormal ambient coordinates. -/
structure NativeBoundaryMetricChart (g : SmoothMetric n M) (p : M) where
  coord : PartialEquiv M (X n)
  open_source : IsOpen coord.source
  ambient : Set (X n)
  open_ambient : IsOpen ambient
  target_eq : coord.target = ambient ∩ inwardHalfSpace n
  point_source : p ∈ coord.source
  point_face : coord p 0 = 0
  smooth : ContMDiffOn J K ∞ coord coord.source
  smooth_inverse : ContMDiffOn K J ∞ coord.symm coord.target
  interior_iff : ∀ x ∈ coord.source, x ∈ (J).interior M ↔ coord x ∈ positiveHalfSpace n
  field : MetricField n
  smooth_field : CalderonN.SmoothMetric ambient field
  normal_field : HasNormalMetricBlock 0 field ambient
  realizes : ∀ x ∈ coord.source, ∀ v w : TangentSpace J x,
    g.inner x v w = metricPair field (coord x) (mfderiv J K coord x v) (mfderiv J K coord x w)

end CalderonPatch
