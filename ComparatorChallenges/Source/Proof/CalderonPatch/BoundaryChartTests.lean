module

public import Proof.CalderonPatch.BoundaryNormalLaplacian
public import Proof.CalderonN.MetricDivergence
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
public import Proof.CalderonPatch.Energy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegrableOn
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
import Proof.CalderonN.SphereFrame
public import Proof.CalderonPatch.DirichletMinimization
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
public import Proof.CalderonPatch.NativeBoundaryMetricChart
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Filter Function Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {m : ℕ}

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

/-- The tangential coordinates on a boundary normal chart. -/
def normalTangentialCoordinates (x : X N) : X m :=
  WithLp.toLp 2 fun i => x ((0 : I N).succAbove i)

/-- The flat-face point at height zero, given its tangential coordinates. -/
def normalFacePoint (z : X m) : X N :=
  WithLp.toLp 2 (Fin.insertNth (0 : I N) 0 (fun i => z i))

/-- The open bottom face of a coordinate half box in its tangential variables. -/
def tangentialBox (a b : I N → ℝ) : Set (X m) :=
  {z | ∀ i : I m, a ((0 : I N).succAbove i) < z i ∧ z i < b ((0 : I N).succAbove i)}

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]

end CalderonPatch
