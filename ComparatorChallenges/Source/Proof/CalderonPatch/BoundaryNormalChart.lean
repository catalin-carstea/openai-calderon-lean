module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Proof.CalderonN.SphereFrame
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Proof.CalderonN.DilationConnection
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
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis)

variable {n : ℕ}

/-- The normal coordinate splits into its foot point on the flat seam
and its height. -/
def boundaryFoot (i : I n) : X n →L[ℝ] X n :=
  ContinuousLinearMap.id ℝ (X n) - (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (axis i)

theorem boundaryFoot_apply (i : I n) (x : X n) : boundaryFoot i x = x - x i • axis i := sorry

theorem boundaryFoot_on_face (i : I n) {x : X n} (hx : x i = 0) : boundaryFoot i x = x := sorry

end CalderonPatch
