module

public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Proof.CalderonN.SphereCoercivity
public import Proof.CalderonN.DilationConnection
public import Proof.CalderonN.DilationHarmonic
public import Proof.CalderonN.Coercivity
public import Proof.CalderonN.Radius
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Matrix.Order
import Proof.CalderonN.Hessian
public import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Data.Nat.Choose.Sum
import Proof.CalderonN.Coordinates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Proof.CalderonN.SphereFrame
import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Proof.CalderonN.HarmonicTestExpansion
public import Proof.CalderonN.FischerFields
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
public import Proof.Archive.AngularCoefficient
public import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Proof.Archive.FischerPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
public import Proof.CalderonN.ZonalProjection
public import Proof.CalderonN.GaussianSphere
public import Proof.CalderonN.SmoothHarmonicWeights
public import Proof.CalderonN.SphereHarmonicBridge
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.PSeries
public import Proof.CalderonN.FramePullback
import Proof.CalderonN.GreenCross
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Proof.CalderonN.SmoothSphereRotation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Proof.CalderonN.HarmonicHilbertDecomposition
public import Proof.CalderonN.CylinderCutoff
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Proof.CalderonN.MovingTrace

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] {normal : I dim}

/-- The prepared sphere family on the fixed conformal cylinder. -/
@[expose] def ConformalCylinderSphereSetup (normal : I dim) (g₁ g₂ : (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim))
    (p : ℕ) (R ε K ρ c₀ floor : ℝ) {m : ℕ} (Mv : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) : Prop :=
  ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ A : TraceAdjoint dim,
    let d := conformalSphereData normal g₁ g₂ E p R lam δ A
    let Y := interior (coordinateCylinder normal)
    (∀ y ∈ Y, 0 < d.radius y ∧ d.radius y < ρ ∧ d.radius y * (beta d.γ d.radius y)^2 ≤ ε) ∧
    Background (ball (0 : (X dim)) 3) K Mv d.γ d.g₁ d.g₂ d.frame ∧
    NormalCoordinates Y (ball (0 : (X dim)) 3) d.γ d.expMap (fun _ => ρ) ∧
    Profile Y d.γ d.frame d.radius floor c₀ Cj

end CalderonN
