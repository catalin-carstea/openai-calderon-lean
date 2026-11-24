module

public import Proof.CalderonN.DilationHarmonic
public import Proof.CalderonN.CovariantHessian
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Order.Star.Real
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ}

/-- Reference metric after dilation and the prescribed scalar change. -/
def conformalReference (σ : X dim → ℝ) (g : MetricField dim) (lam : ℝ) (y : X dim) : Mat dim :=
  σ y • dilatedMetric g lam y

end CalderonN
