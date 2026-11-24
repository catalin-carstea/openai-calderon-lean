module

public import Proof.CalderonN.MovingBallFamilies
public import Proof.CalderonN.NormalBallChart
public import Proof.CalderonN.MetricPullback
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Tactic.FieldSimp
import Proof.CalderonN.Chart
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Proof.CalderonN.DilationHarmonic
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.ParametricBallVelocityAdjoint
public import Proof.CalderonN.SphereFrame

/-! Adapted from `ActualMovingTraceAdjoint` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Apply the fixed-ball real adjoint to the two components of the datum
in the angular frame, and restore the physical velocity's radius factor. -/
@[expose] def actualMovingTraceAdjoint
    (γ g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ) : (TraceAdjoint dim) :=
  fun i y φ w =>
    let m := movingBallMetric g E e r
    let V := movingBallScaledVelocity γ E e r i
    let p := movingBallToFrame γ e (y,w)
    let a := parametricBallVelocityAdjoint m V (fun z => (φ (frameVector e y z.2)).re) p
    let b := parametricBallVelocityAdjoint m V (fun z => (φ (frameVector e y z.2)).im) p
    ⟨(r y)⁻¹*a,(r y)⁻¹*b⟩

end CalderonN
