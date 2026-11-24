module

public import Proof.CalderonN.NormalBallChart
public import Proof.CalderonN.MetricPullback
import Proof.CalderonN.SphereFrame
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
import Proof.CalderonN.MovingTrace
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Proof.CalderonN.Chart
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.FrameOperators
public import Proof.CalderonN.LinearMetric

/-! Adapted from `NormalizedBallMetric` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Metric
open scoped ContDiff Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The normal chart derivative with its explicit scalar radius removed. -/
@[expose] def normalizedBallDerivative (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (y : (X dim)) (r : ℝ) (z : (X dim)) :
    (X dim) →L[ℝ] (X dim) :=
  (fderiv ℝ (fun v => E (y,v)) (r • frameVector e y z)).comp (frameVectorL (e y))

/-- The first metric on the fixed ball with the scaling factor removed.
It is defined even at zero radius. -/
@[expose] def normalizedBallMetric (g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (y : (X dim)) (r : ℝ) (z : (X dim)) : (Mat dim) :=
  let M := coordinateMatrix (normalizedBallDerivative E e y r z)
  Mᵀ * g (normalBallChartMap E e y r z) * M

end CalderonN
