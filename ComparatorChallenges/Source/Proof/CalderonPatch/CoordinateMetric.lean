module

public import Proof.CalderonPatch.MatchedCoordinates
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Tactic.Ring
import Proof.CalderonN.LinearMetric
import Proof.CalderonN.Chart
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
public import Proof.CalderonN.Coordinates
public import Proof.CalderonPatch.Energy

@[expose] public section

noncomputable section
open Bundle Matrix Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X axis MetricField)

variable {n : ℕ} [NeZero n] {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]

local notation "J" => (𝓡∂ n)
local notation "K" => 𝓘(ℝ, X n)

/-- The native metric in an interior chart, expressed in its coordinate basis. -/
def coordinateMetric (g : SmoothMetric n M) (e : OpenPartialHomeomorph M (X n)) : MetricField n :=
  fun x i j =>
    let D := mfderiv K J e.symm x
    g.inner (e.symm x) (D (axis i)) (D (axis j))

end CalderonPatch
