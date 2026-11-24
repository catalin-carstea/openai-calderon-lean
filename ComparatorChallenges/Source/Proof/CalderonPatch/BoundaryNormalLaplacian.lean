module

public import Proof.CalderonPatch.CompactSecondJet
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic
public import Proof.CalderonPatch.NativeLaplace
import Proof.CalderonN.CovariantHessian
public import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

noncomputable section
open Filter Matrix Set
open scoped Topology

namespace CalderonPatch

open CalderonN (I X Mat MetricField axis coordDeriv christoffel laplace)

variable {n : ℕ} {U : Set (X n)} {g : MetricField n} {i : I n}

/-- The (i)-th coordinate is the unit normal and orthogonal to the
coordinate slices. -/
def HasNormalMetricBlock (i : I n) (g : MetricField n) (U : Set (X n)) : Prop :=
  ∀ x ∈ U, ∀ j, g x i j = if i = j then 1 else 0

end CalderonPatch
