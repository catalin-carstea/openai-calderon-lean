module

public import Proof.CalderonPatch.MatchedCapMetrics
public import Proof.CalderonPatch.CapShift
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
public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Proof.CalderonPatch.NativeBoundaryMetricChart
public import Proof.CalderonPatch.SignedCapBox
public import Proof.CalderonN.Chart
public import Proof.CalderonPatch.BoundaryChartExtension
public import Proof.CalderonPatch.CoordinateMetricSection
public import Proof.CalderonPatch.Energy
public import Proof.CalderonPatch.NativeNormalChart

public section

noncomputable section
open Metric Set Filter
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField chartDerivativeWord metricPair)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "Zt" => boundaryTangentPlane (0 : I n)
local notation "H" => inwardHalfSpace n

/-- One side of the cap, with its unpushed signed metric and its
relationship to the original embedding. -/
structure AttachedCapSide (A : ProductBoundaryChart (n := n) (M := M) (Z := Zt))
    (γ : MetricField n) (G : SmoothMetric n M) (cap : Set M) (embed : M → M)
    (height : Zt → ℝ) (push : (Zt × ℝ) ≃ (Zt × ℝ)) where
  shift : CapShift A
  cap_eq : cap = shift.cap
  embed_eq : embed = shift.embed
  height_eq : shift.capHeight = height
  push_eq : shift.coordinateShift = push
  field : MetricField n
  smooth_field : CalderonN.SmoothMetric ((inwardChartSplit (n := n)) ⁻¹' A.ambient) field
  inward_field : EqOn field γ H
  realizes : ∀ x ∈ A.coord.source,
    G.inner x = nativeCoordinateBilinear field
      ((inwardChartSplit (n := n)).symm ∘ push.symm ∘ A.coord) x

/-- The shared box and vertical push, together with both native
signed readings and their identifications on the cap and the seam. -/
structure CommonCapCoordinates {W : Set (Zt × ℝ)} {z₀ : Zt}
    (A₁ A₂ : ProductBoundaryChart (n := n) (M := M) (Z := Zt))
    (γ₁ γ₂ : MetricField n) (G₁ G₂ : SmoothMetric n M)
    (capMap : OpenPartialHomeomorph M M) (embed₁ embed₂ : M → M) where
  box : SignedCapBox W z₀
  height : Zt → ℝ
  smooth_height : ContDiff ℝ ∞ height
  height_bound : ∀ z, 0 ≤ height z ∧ height z < box.radius
  height_support : {z | 0 < height z} = ball z₀ box.radius
  push : (Zt × ℝ) ≃ (Zt × ℝ)
  smooth_push : ContDiff ℝ ∞ push
  smooth_push_inverse : ContDiff ℝ ∞ push.symm
  push_tangential : ∀ q, (push q).1 = q.1
  push_seam : ∀ z, push (z,0) = (z,height z)
  push_boundary : ∀ z, push (z,-height z) = (z,0)
  push_monotone : ∀ z, StrictMono (fun t => (push (z,t)).2)
  first : AttachedCapSide A₁ γ₁ G₁ capMap.target embed₁ height push
  second : AttachedCapSide A₂ γ₂ G₂ capMap.source embed₂ height push
  charts_map : (capMap : M → M) = A₁.coord.symm ∘ A₂.coord
  fields_eq : EqOn first.field second.field Hᶜ
  original_fields_eq : EqOn γ₁ γ₂
    (((inwardChartSplit (n := n)) ⁻¹' W) ∩ {x | x (0 : I n) = 0})

end CalderonPatch
