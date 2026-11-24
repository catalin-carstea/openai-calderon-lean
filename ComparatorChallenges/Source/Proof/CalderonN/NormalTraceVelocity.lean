module

public import Proof.CalderonN.NormalizedBallMetric
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.LinearMetric
public import Proof.CalderonN.SphereFrame

/-! Adapted from `NormalTraceVelocity` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Matrix
open scoped ContDiff Matrix Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Radius times the moving physical boundary velocity in fixed-ball
coordinates. The independent parameter `b` is the derivative of the
radius along the specified base direction. -/
@[expose] def scaledNormalTraceVelocity (γ : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (y : (X dim)) (s b : ℝ) (z a : (X dim)) : (X dim) :=
  let w := frameVector e y z
  let D := coordinateMatrix (normalizedBallDerivative E e y s z)
  let v := fderiv ℝ E (y,s • w) (a,b • w - s • connection γ y a w)
  WithLp.toLp 2 (D⁻¹ *ᵥ fun i => v i)

end CalderonN
