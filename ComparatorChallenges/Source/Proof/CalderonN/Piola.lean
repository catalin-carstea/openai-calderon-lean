module

public import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricVolumeDifferential
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

/-! Adapted from the reviewed Proposition 5.3 release's
`Proof/Archive/CoordinatePiolaCovariance.lean`,
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. -/

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Operator

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def coordinateJacobian (F : (X dim) → (X dim)) (x : (X dim)) : (Mat dim) :=
  coordinateMatrix (fderiv ℝ F x)

end CalderonN
