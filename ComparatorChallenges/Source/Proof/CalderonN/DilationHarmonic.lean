module

public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

public section

noncomputable section
open Set Filter
open scoped ContDiff BigOperators Topology

namespace CalderonN

variable {n : ℕ}

/- Port of the chart dilation from the 3D Theorem 3.1 release (55d37bfe).
Coordinate and Hessian regularity helpers retain their earlier proof bodies. -/

@[expose] def dilatedMetric (g : MetricField n) (lam : ℝ) (y : X n) : Mat n :=
  g (lam • y)

/-- The common affine part is subtracted before the quadratic rescaling. -/
@[expose] def renormalizedHarmonic (c : ℝ) (L : X n →L[ℝ] ℝ) (u : X n → ℝ) (lam : ℝ) (y : X n) : ℝ :=
  (lam ^ 2)⁻¹ * (u (lam • y) - (c + lam * L y))

end CalderonN
