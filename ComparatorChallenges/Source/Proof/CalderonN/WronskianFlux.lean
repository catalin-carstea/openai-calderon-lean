module

public import Proof.CalderonN.MetricDivergence
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The Wronskian as a chart vector density. Its outward flux gives the
Green transfer with the Riemannian volume and first metric. -/
@[expose] def wronskianFlux (g : (MetricField dim)) (u k : (X dim) → ℝ) (x : (X dim)) : (X dim) :=
  WithLp.toLp 2 fun i => k x * divergenceFlux g u x i - u x * divergenceFlux g k x i

end CalderonN
