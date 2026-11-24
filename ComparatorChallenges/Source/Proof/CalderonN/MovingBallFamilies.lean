module

public import Proof.CalderonN.NormalTraceVelocity
import Proof.CalderonN.Coordinates
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Proof.CalderonN.Coercivity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
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
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Group.Integral
import Proof.CalderonN.Piola
import Proof.CalderonN.SpherePolarIntegration
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Proof.CalderonN.MetricDivergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Proof.CalderonN.NormalFluxDensity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Separation.Regular
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Topology.Algebra.Group.Order
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.Extend
import Proof.CalderonN.SmoothSphereRotation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.Banach
import Proof.CalderonN.ScaledGreenDatumJets
public import Proof.CalderonN.ParametricBallVelocityAdjoint
public import Proof.CalderonN.FixedBallGreenPairing
import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Proof.CalderonN.NormalizedBallMetric
public import Proof.CalderonN.SphereFrame

/-! Adapted from `MovingBallFamilies` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000
noncomputable section
open Set Metric
open scoped ContDiff Topology Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The normalized pullback on the fixed unit ball at its actual radius. -/
@[expose] def movingBallMetric (g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (r : (X dim) → ℝ) (q : (X dim) × (X dim)) : (Mat dim) :=
  normalizedBallMetric g E e q.1 (r q.1) q.2

/-- The same normalization keeps one explicit power of the physical radius
outside the velocity. -/
@[expose] def movingBallScaledVelocity (γ : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (r : (X dim) → ℝ) (i : (I dim)) (q : (X dim) × (X dim)) : (X dim) :=
  scaledNormalTraceVelocity γ E e q.1 (r q.1) (coordDeriv i r q.1) q.2 (axis i)

/-- Convert between physical tangent vectors and Euclidean angular coordinates. -/
@[expose] def movingBallToFrame (γ : (MetricField dim)) (e : (Frame dim)) (q : (X dim) × (X dim)) : (X dim) × (X dim) :=
  (q.1,frameCoordinates γ q.1 (e q.1) q.2)

end CalderonN
