module

public import Proof.CalderonN.DilationConnection
public import Proof.CalderonN.FixedTube.Phase
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import Proof.CalderonN.MetricConnection
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology

namespace CalderonN

variable {dim : ℕ} {normal : I dim}
open FixedTube

/-- The parabolic height in the tangent-normal chart. -/
def parabolicHeight (normal : I dim) (y : X dim) : ℝ := tubeHeight normal 0 1 y

def depthScale (normal : I dim) (L : ℝ) (y : X dim) : ℝ :=
  Real.exp (-2 * L * parabolicHeight normal y)

/-- The integral of the conformal scale from height one eighth. -/
def conformalDepth (normal : I dim) (L : ℝ) (y : X dim) : ℝ :=
  (Real.exp (-L / 4) - depthScale normal L y) / (2 * L)

end CalderonN
