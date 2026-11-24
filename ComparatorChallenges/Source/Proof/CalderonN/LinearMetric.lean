module

public import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

public section

/-! LinearMetric from the checked 3D Theorem 3.1 release 55d37bfe, with arbitrary ambient dimension. -/

noncomputable section
open Set Matrix
open scoped ContDiff Matrix BigOperators

namespace CalderonN

variable {n : ℕ} [NeZero n]

/-- Matrix of a linear change of the common Euclidean coordinates. -/
@[expose] def coordinateMatrix (A : (X n) →L[ℝ] (X n)) : (Mat n) :=
  Matrix.toEuclideanLin.symm A.toLinearMap

end CalderonN
