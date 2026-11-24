module

public import Proof.CalderonN.Coercivity
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

set_option maxSynthPendingDepth 10

public section

/- CoordinateTensors, MetricConnection, HorizontalGeometry and FrameConnection
   from Proposition 5.3 check f308cb9d. The operations are the protected
   metric, connection and horizontal derivative in dimension n. -/
noncomputable section
open Set
open scoped ContDiff MatrixOrder Matrix.Norms.L2Operator
namespace CalderonN
variable {n : ℕ}

/-- The coordinate metric as a continuous bilinear form. -/
@[expose] def metricBilinear (g : (MetricField n)) (y : (X n)) : (X n) →L[ℝ] (X n) →L[ℝ] ℝ :=
  ∑ i, ∑ j, (g y i j) • (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)

end CalderonN
