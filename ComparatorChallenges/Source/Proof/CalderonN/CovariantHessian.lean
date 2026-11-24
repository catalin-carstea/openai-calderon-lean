module

public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set Matrix
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ}

@[expose] def metricHessian (g : (MetricField dim)) (f : (X dim) → ℝ) (y : (X dim)) (i j : (I dim)) : ℝ :=
  hessian f y i j - ∑ k, christoffel g y k i j * coordDeriv k f y

@[expose] def covectorSq (g : (MetricField dim)) (f : (X dim) → ℝ) (y : (X dim)) : ℝ :=
  ∑ i, ∑ j, (g y)⁻¹ i j * coordDeriv i f y * coordDeriv j f y

end CalderonN
