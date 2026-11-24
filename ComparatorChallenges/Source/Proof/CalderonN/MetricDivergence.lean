module

public import Proof.CalderonN.MetricVolumeDifferential
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

/-! Adapted from `Calderon/MetricDensityConnection.lean` and
`Calderon/MetricHessianDivergence.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

public section

noncomputable section
open Set
open scoped BigOperators Matrix.Norms.Operator ContDiff
namespace CalderonN

variable {n : ℕ}

@[expose] def divergenceCoeff (g : (MetricField n)) (y : (X n)) (i j : (I n)) : ℝ :=
  chartVolume g y * (g y)⁻¹ i j

@[expose] def divergenceFlux (g : (MetricField n)) (f : (X n) → ℝ) (y : (X n)) (i : (I n)) : ℝ :=
  ∑ j, divergenceCoeff g y i j * coordDeriv j f y

end CalderonN
