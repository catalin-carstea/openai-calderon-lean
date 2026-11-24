module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Tactic.FieldSimp
public import Proof.CalderonN.Coordinates

/-! Adapted from `Calderon/MetricVolumeDifferential.lean` and
`Calderon/MetricInverseDifferential.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

noncomputable section
open scoped Matrix.Norms.Operator ContDiff
namespace CalderonN

variable {n : ℕ}

def chartVolume (g : MetricField n) (x : X n) : ℝ := Real.sqrt (g x).det

end CalderonN
