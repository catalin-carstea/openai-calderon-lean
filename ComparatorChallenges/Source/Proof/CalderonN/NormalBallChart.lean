module

public import Proof.CalderonN.NormalInverse
public import Proof.CalderonN.SphereFrame
import Proof.CalderonN.Chart
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Proof.CalderonN.FrameOperators
import Proof.CalderonN.FramePullback
public import Proof.CalderonN.LinearMetric
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Rescale the literal reference-metric normal ball to the fixed
Euclidean unit ball. The derivative includes the physical radius. -/
@[expose] def normalBallChartMap (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (y : (X dim)) (r : ℝ) (z : (X dim)) : (X dim) :=
  E (y,r • frameVector e y z)

end CalderonN
