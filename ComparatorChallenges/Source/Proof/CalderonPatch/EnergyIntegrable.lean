module

public import Proof.CalderonPatch.BoundaryChartTests
public import Proof.CalderonPatch.NativeLaplace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Proof.CalderonN.LinearMetric
public import Proof.CalderonPatch.CoordinateMetric
public import Proof.CalderonN.Coordinates
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import Proof.CalderonPatch.MetricDualEnergy
public import Proof.CalderonN.CovariantHessian
public import Proof.CalderonN.StrictMetricWeight
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Proof.CalderonN.Chart
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Proof.CalderonN.SphereFrame
public import Proof.CalderonPatch.DirichletMinimization
public import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
public import Proof.CalderonPatch.NativeBoundaryMetricChart
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Tactic.Linarith
public import Proof.CalderonPatch.Energy

public section

noncomputable section
open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (I X InteriorMetricChart MetricField chartMetricGradient chartVolume chartVolumeMeasure coordDeriv)

variable {n : ℕ} [NeZero n] {M : Type*}
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

variable [T2Space M] [CompactSpace M]

local notation "H" => inwardHalfSpace n

/-- The polarized energy of smooth functions is integrable against
the metric volume on a compact manifold with boundary. -/
theorem integrable_energyPairingDensity
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
    (g : SmoothMetric (m + 1) M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    {u v : M → ℝ} (hu : ContMDiff (𝓡∂ (m + 1)) R ∞ u) (hv : ContMDiff (𝓡∂ (m + 1)) R ∞ v) :
    Integrable (energyPairingDensity g u v) μ := sorry

end CalderonPatch
