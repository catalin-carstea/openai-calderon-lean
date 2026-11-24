module

public import Proof.CalderonPatch.DirichletWeak
public import Proof.CalderonPatch.EnergyIntegrable
public import Proof.CalderonPatch.NativeBoundaryMetricChart
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Proof.CalderonPatch.CoordinateMetric
public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Proof.CalderonPatch.NativeLaplace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Proof.CalderonN.LinearMetric
import Proof.CalderonPatch.Energy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Geometry.Manifold.Algebra.Structures
public import Proof.CalderonPatch.CompactSecondJet
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.LinearAlgebra.Isomorphisms
public import Proof.CalderonN.Coordinates
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LSum
public import Proof.CalderonN.ChartSchwarzWords
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Proof.CalderonN.CovariantHessian
import Proof.CalderonN.MetricVolumeDifferential
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Proof.CalderonN.DilationHarmonic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.NormNum
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Proof.CalderonN.FrameOperators
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Proof.CalderonN.Coercivity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Extend
import Proof.CalderonN.SmoothSphereRotation
import Proof.CalderonN.SphereHarmonicBridge
import Proof.Archive.FischerPolynomial
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Proof.CalderonN.HarmonicHilbertDecomposition
import Proof.CalderonN.NormalFluxDensity
import Proof.CalderonN.GaussianSphere
import Proof.CalderonN.SmoothHarmonicWeights
import Proof.CalderonN.SmoothSphereRotationProjection
import Mathlib.Algebra.DirectSum.Module
import Mathlib.MeasureTheory.Group.Integral
import Proof.CalderonN.Piola
import Proof.CalderonN.SpherePolarIntegration
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Separation.Regular
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Topology.Algebra.Group.Order
import Mathlib.Topology.MetricSpace.Thickening
import Proof.CalderonN.ParametricBallConormal
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.Banach
import Proof.CalderonN.BoundedHarmonicShift
import Proof.CalderonN.HarmonicMultiplier
import Proof.CalderonN.FixedBallGreenPairing
import Proof.CalderonN.ConormalDecomposition
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Proof.CalderonN.SphereFrame
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
import Proof.CalderonN.MovingTrace
import Proof.CalderonN.MetricConnection
import Proof.Archive.AngularCoefficient
import Proof.CalderonN.FischerFields
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Add
import Proof.CalderonN.FramePullback
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Abel
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Proof.CalderonN.ZonalProjection
import Proof.CalderonN.SmoothSphereFields
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Proof.CalderonN.NormalBallChart
import Proof.CalderonN.MetricPullback
import Proof.CalderonN.NormalTraceVelocity
import Proof.CalderonN.NormalizedBallMetric
import Proof.CalderonN.ParametricBallVelocityAdjoint
import Proof.CalderonN.ActualMovingTraceAdjoint
import Proof.CalderonN.GreenCross
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Analysis.Normed.Operator.Basic
import Proof.CalderonN.NormalInverse
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Proof.CalderonN.HarmonicTestExpansion
import Proof.CalderonN.ModelOutputLimits
import Proof.CalderonN.HarmonicDerivativeOperator
import Proof.CalderonN.SmoothAmbientAngularCasimir
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
public import Proof.CalderonN.GreenRestriction
public import Proof.CalderonPatch.DirichletHilbert

public section

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Manifold Matrix.Norms.Elementwise

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)

/-- Analytic properties of the actual canonical weak inverse used by
the Green construction. Both regularity statements describe smooth
representatives of the exact almost-everywhere class of the inverse. -/
structure NativeInverseRegularity (D : DirichletData m M) : Prop where
  smooth_solution :
    ∀ (f : Lp ℝ 2 D.volume) (q : M → ℝ), ContMDiff J R ∞ q →
      (f : M → ℝ) =ᵐ[D.volume] q →
      ∃ u : M → ℝ, ContMDiff J R ∞ u ∧ EqOn u 0 ((J).boundary M) ∧
        EqOn (-nativeLaplace D.metric u) q ((J).interior M) ∧
        (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume] u
  local_zero_forcing :
    ∀ (U : Set M), IsOpen U → ∀ f : Lp ℝ 2 D.volume,
      (f : M → ℝ) =ᵐ[D.volume.restrict U] 0 →
      ∃ u : M → ℝ, ContMDiffOn J R ∞ u U ∧ EqOn u 0 (U ∩ (J).boundary M) ∧
        EqOn (nativeLaplace D.metric u) 0 (U ∩ (J).interior M) ∧
        (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict U] u

end CalderonPatch
