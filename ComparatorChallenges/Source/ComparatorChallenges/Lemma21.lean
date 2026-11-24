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
public import Proof.CalderonPatch.DirichletHilbert

public section

open MeasureTheory Set
open scoped ContDiff Manifold
open CalderonN (I chartDerivativeWord)
open CalderonPatch

namespace CalderonPaper

/-- Lemma 2.1 of the September 24, 2026 manuscript. A paired box
represents the two normal coordinate systems with the same tangential
coordinates at the boundary. A derivative word specifies an arbitrary
coordinate partial derivative, including mixed derivatives. -/
theorem lemma21 {m : ℕ} (hn : 3 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (d₁ d₂ : DirichletData m M)
    {Γ : Set ((𝓡∂ (m+1)).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (p : (𝓡∂ (m+1)).boundary M) (hp : p ∈ Γ)
    (B : PairedNativeBoundaryBox d₁.metric d₂.metric Γ p) :
    ∀ (w : List (I (m+1))) (i j : I (m+1)),
      EqOn
        (fun y => chartDerivativeWord w (fun z => B.first.field z i j) (normalFacePoint y))
        (fun y => chartDerivativeWord w (fun z => B.second.field z i j) (normalFacePoint y))
        (tangentialBox B.boxLower B.boxUpper) := sorry

end CalderonPaper
