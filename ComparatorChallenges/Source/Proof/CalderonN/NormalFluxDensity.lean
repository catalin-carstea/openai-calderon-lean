module

public import Proof.CalderonN.NormalBallChart
public import Proof.CalderonN.MetricPullback
import Mathlib.Tactic
public import Proof.CalderonN.NormalGreenFlux
public import Proof.CalderonN.FixedBallGreenPairing
public import Proof.CalderonN.Chart
public import Proof.CalderonN.Coercivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Proof.CalderonN.SphereFrame
import Proof.CalderonN.GreenCross
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Algebra.Order.Star.Real
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
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
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.SpherePolarIntegration

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option backward.isDefEq.respectTransparency.types false

/-- The normalization from surface measure to the protected probability
measure multiplies the ordinary conormal density by the sphere area. -/
@[expose] def unitSphereArea (dim : ℕ) [NeZero dim] : ℝ := ((chartSurfaceMeasure dim) univ).toReal

end CalderonN
