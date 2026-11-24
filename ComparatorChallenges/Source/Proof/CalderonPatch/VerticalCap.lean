module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace CalderonPatch

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- In the pushed-in realization of a cap, the original seam is the
graph of the nonnegative bump. -/
@[expose] def pushedCap (b : Z → ℝ) : Set (Z × ℝ) := {p | 0 < p.2 ∧ p.2 < b p.1}

end CalderonPatch
