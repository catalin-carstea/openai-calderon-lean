module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Tactic
public import Proof.CalderonN.FixedTube.Phase
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Proof.CalderonN.ProductMetricHessian
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Proof.CalderonN.DilationHarmonic
public import Proof.CalderonN.StrictMetricWeight
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Proof.CalderonN.GreenCross
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Proof.CalderonN.MetricVolumeDifferential
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Proof.CalderonN.CovariantHessian
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

@[expose] def fixedSeparationSet (B d : ℝ) : Set ((X dim) × (X dim)) :=
  {p | ‖p.1‖ ≤ B ∧ ‖p.2‖ ≤ B ∧ d ≤ ‖p.1-p.2‖}

end CalderonN.FixedTube
