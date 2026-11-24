module

public import Proof.CalderonN.CovariantHessian
public import Proof.CalderonN.MetricVolumeDifferential
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Order.Star.Real
import Proof.CalderonN.MetricDivergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff BigOperators

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def chartMetricGradient (g : (MetricField dim)) (φ : (X dim) → ℝ) (x : (X dim)) : (X dim) :=
  WithLp.toLp 2 fun i => ∑ j, (g x)⁻¹ i j * coordDeriv j φ x

end CalderonN
