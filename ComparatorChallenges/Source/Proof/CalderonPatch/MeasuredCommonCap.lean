module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Proof.CalderonPatch.BoundaryNormalLaplacian
import Proof.CalderonN.CovariantHessian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Proof.CalderonPatch.BoundaryChartTests
public import Proof.CalderonPatch.NativeBoundaryMetricChart
public import Proof.CalderonPatch.CoordinateMetric
public import Proof.CalderonN.Chart
public import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
public import Proof.CalderonPatch.DirichletWeak
public import Proof.CalderonPatch.EnergyIntegrable
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Proof.CalderonPatch.NativeLaplace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Proof.CalderonN.LinearMetric
import Proof.CalderonPatch.Energy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Geometry.Manifold.Algebra.Structures
import Proof.CalderonPatch.DirichletMinimization
import Proof.CalderonN.Coordinates
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Proof.CalderonN.GreenCross
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Proof.CalderonN.DilationHarmonic
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Proof.CalderonN.GreenRestriction
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LSum
import Proof.CalderonN.ChartSchwarzWords
import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Proof.CalderonPatch.PairedNativeBoundaryBox
public import Proof.CalderonPatch.AttachedCommonCap
public import Proof.CalderonPatch.BoundaryChartExtension
public import Proof.CalderonPatch.CapShift
public import Proof.CalderonPatch.DirichletHilbert
public import Proof.CalderonPatch.MatchedCapMetrics
public import Proof.CalderonPatch.MatchedCoordinates
public import Proof.CalderonPatch.NativeNormalChart
public import Proof.CalderonPatch.ReturnToOriginal

public section
noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X chartDerivativeWord)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "Z" => X (n+1)
local notation "Y" => X n
local notation "J" => 𝓡∂ (n+1)
local notation "L" => (inwardChartSplit (n := n+1))
local notation "P" => boundaryTangentPlane (0 : I (n+1)) × ℝ

/-- A common cap recovered from the measurements, retaining the source
normal charts for the boundary Green formula. -/
structure MeasuredCommonCap (d₁ d₂ : DirichletData n M) (Γ : Set ((J).boundary M)) where
  center : (J).boundary M
  charts : PairedNativeBoundaryBox d₁.metric d₂.metric Γ center
  ambient : Set P
  open_ambient : IsOpen ambient
  subset_first : ambient ⊆ charts.prod₁.ambient
  subset_second : ambient ⊆ charts.prod₂.ambient
  subset_signed : L ⁻¹' ambient ⊆ charts.signed
  firstMetric : SmoothMetric (n+1) M
  secondMetric : SmoothMetric (n+1) M
  capMap : OpenPartialHomeomorph M M
  connected_source : IsConnected capMap.source
  connected_target : IsConnected capMap.target
  source_interior : capMap.source ⊆ (J).interior M
  target_interior : capMap.target ⊆ (J).interior M
  isometry : IsLocalMetricIsometry firstMetric secondMetric capMap
  firstCopy : OriginalCopy d₁.metric firstMetric capMap.target
  secondCopy : OriginalCopy d₂.metric secondMetric capMap.source
  patch : Set ((J).boundary M)
  open_patch : IsOpen patch
  nonempty_patch : patch.Nonempty
  patch_subset : patch ⊆ Γ
  traces_supported : ∀ w : M → ℝ, EqOn w 0 ((J).boundary M) →
    tsupport (fun p : (J).boundary M => w (firstCopy.embed p)) ⊆ Γ ∧
    tsupport (fun p : (J).boundary M => w (secondCopy.embed p)) ⊆ Γ
  seam : ∀ e : OpenPartialHomeomorph M M, e.source = (J).interior M → EqOn e capMap capMap.source →
    ∀ p ∈ patch, secondCopy.embed p ∈ e.source ∧ e (secondCopy.embed p) = firstCopy.embed p
  coordinates : CommonCapCoordinates (W := ambient) (z₀ := (charts.prod₂.coord center).1)
    (charts.prod₁.restrictAmbient open_ambient subset_first)
    (charts.prod₂.restrictAmbient open_ambient subset_second) charts.first.field charts.second.field
    firstMetric secondMetric capMap firstCopy.embed secondCopy.embed

end CalderonPatch
