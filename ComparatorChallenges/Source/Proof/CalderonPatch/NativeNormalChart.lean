module

public import Proof.CalderonPatch.CapShift
public import Proof.CalderonPatch.BoundaryChartExtension
public import Proof.CalderonPatch.BoundaryNormalChart
public import Proof.CalderonN.Chart
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic
import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Proof.CalderonN.SphereFrame
import Mathlib.Tactic.Linarith
public import Proof.CalderonPatch.CoordinateMetric
public import Proof.CalderonN.MetricPullback
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Proof.CalderonN.LinearMetric
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Proof.CalderonN.Coordinates

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField pullbackMetric)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "XH" => boundaryTangentPlane (0 : I n)

/-- The product chart uses inward rather than outward height. -/
def inwardChartSplit : X n ≃L[ℝ] XH × ℝ :=
  (boundaryChartSplit (0 : I n)).trans
    ((ContinuousLinearEquiv.refl ℝ XH).prodCongr (ContinuousLinearEquiv.neg ℝ))

end CalderonPatch
