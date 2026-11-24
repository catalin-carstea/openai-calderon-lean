module

public import Proof.CalderonPatch.Energy
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set
open scoped Manifold

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]

local notation "T" => TangentSpace (𝓡∂ n)

/-- Positive definiteness realizes every covector by a unique metric-dual vector. -/
theorem existsUnique_metricDual (g : SmoothMetric n M) (x : M) (a : T x →L[ℝ] ℝ) :
    ∃! w : T x, ∀ v : T x, g.inner x w v = a v := sorry

/-- Raising a covector by the metric. -/
def metricDual (g : SmoothMetric n M) (x : M) (a : T x →L[ℝ] ℝ) : T x :=
  (existsUnique_metricDual g x a).exists.choose

end CalderonPatch
