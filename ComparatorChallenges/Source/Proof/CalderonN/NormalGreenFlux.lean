module

public import Proof.CalderonN.NormalInverse
public import Proof.CalderonN.SphereFrame
import Proof.CalderonN.Chart
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Proof.CalderonN.FrameOperators
import Proof.CalderonN.FramePullback
public import Proof.CalderonN.GreenCross
public import Proof.CalderonN.FixedKernelIntegral
public import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Proof.CalderonN.DilationHarmonic
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Proof.CalderonN.NormalBallChart
public import Proof.CalderonN.MetricPullback
public import Proof.CalderonN.WronskianFlux
public import Proof.CalderonN.Piola
public import Proof.CalderonN.SpherePolarIntegration
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Proof.CalderonN.LinearMetric
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Function.Jacobian
public import Proof.CalderonN.Coordinates

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The transfer flux on the actual normal sphere, expressed in its
fixed unit-ball coordinates and in the pullback of the first metric. -/
@[expose] def normalSphereGreenFlux (g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ)
    (G : (X dim) × (X dim) → ℝ) (y : (X dim)) (u : (X dim) → ℝ) : ℝ :=
  let F := normalBallChartMap E e y (r y)
  unitSphereFlux (wronskianFlux (pullbackMetric g F) (u ∘ F) fun z => G (F z,y))

end CalderonN
