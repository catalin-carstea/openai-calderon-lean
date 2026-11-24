module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.DilationConnection
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic
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
public import Proof.CalderonN.MovingTrace
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ}

/-- The interior of the normal velocity disks, with the same radius as
the protected normal-coordinate witness. -/
@[expose] def normalVelocityDomain (Y : Set (X dim)) (γ : (MetricField dim)) (R : ℝ) : Set ((X dim) × (X dim)) :=
  {p | p.1 ∈ Y ∧ metricPair γ p.1 p.2 p.2 < R^2}

/-- The physical pair has the center in the second factor. -/
@[expose] def normalPairMap (expMap : (X dim) × (X dim) → (X dim)) (p : (X dim) × (X dim)) : (X dim) × (X dim) :=
  (expMap p,p.1)

@[expose] def normalPairDomain (Y : Set (X dim)) (γ : (MetricField dim)) (R : ℝ)
    (expMap : (X dim) × (X dim) → (X dim)) : Set ((X dim) × (X dim)) :=
  normalPairMap expMap '' normalVelocityDomain Y γ R

end CalderonN
