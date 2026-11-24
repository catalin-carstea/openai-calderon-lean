module

public import Proof.CalderonN.ConformalDepth
public import Proof.CalderonN.CovariantHessian
public import Proof.CalderonN.Radius
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coercivity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Proof.CalderonN.SmoothMetricFrame
public import Proof.CalderonN.DilationHarmonic
import Proof.CalderonN.StrictMetricWeight
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NormNum
import Proof.CalderonN.DilationConnection
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Transform
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Mul
import Proof.CalderonN.MovingTrace
public import Proof.CalderonN.Coordinates

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
variable {normal : I dim}

/-- The actual sphere data after the fixed conformal normalization and dilation. -/
@[expose] def conformalSphereData (normal : I dim) (g₁ g₂ : (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim))
    (p : ℕ) (R lam δ : ℝ) (A : (TraceAdjoint dim)) : (Data dim) :=
  let γ := conformalReference (depthScale normal 4) g₁ lam
  ⟨γ, dilatedMetric g₁ lam, dilatedMetric g₂ lam, fun y => smoothMetricFrame (γ y),
    shrinkingRadius R p (conformalDepth normal 4) δ, E lam, A⟩

end CalderonN
