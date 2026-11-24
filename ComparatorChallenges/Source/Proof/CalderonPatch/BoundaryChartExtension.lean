module

public import Proof.CalderonPatch.Energy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Proof.CalderonN.Chart
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Proof.CalderonN.LinearMetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Proof.CalderonN.Coordinates
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Compactness.Compact
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.Linarith
public import Proof.CalderonPatch.BoundaryNormalChart
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set

public section

noncomputable section
open Filter Matrix Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X Mat MetricField axis)

variable {n : ℕ}

/-- The tangential vector space of a flat coordinate face. -/
abbrev boundaryTangentPlane (i : I n) : Submodule ℝ (X n) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap.ker

private theorem boundaryFoot_coordinate_zero (i : I n) (x : X n) : boundaryFoot i x i = 0 := sorry

private def boundaryLinearSplit (i : I n) : X n →L[ℝ] boundaryTangentPlane i × ℝ :=
  ((boundaryFoot i).codRestrict (boundaryTangentPlane i) (boundaryFoot_coordinate_zero i)).prod
    (-EuclideanSpace.proj i)

/-- Split a flat face into its tangential coordinates and the signed
normal coordinate, using the negative inward sign for the half-space extension. -/
def boundaryChartSplit (i : I n) : X n ≃L[ℝ] boundaryTangentPlane i × ℝ := by
  let A := boundaryLinearSplit i
  have hAxis : axis i i = 1 := by simp [axis]
  have hAij : Function.Injective A := (injective_iff_map_eq_zero A).mpr (fun x hx => by
    have hxcoord := congrArg (fun q : boundaryTangentPlane i × ℝ => q.2) hx
    have hf := congrArg (fun q : boundaryTangentPlane i × ℝ => (q.1 : X n)) hx
    change -x i = 0 at hxcoord
    change boundaryFoot i x = 0 at hf
    rwa [boundaryFoot_on_face _ (neg_eq_zero.mp hxcoord)] at hf)
  have hAs : Function.Surjective A := by
    rintro ⟨z,t⟩
    let x : X n := (z : X n) - t • axis i
    have hz : (z : X n) i = 0 := z.property
    have hxi : x i = -t := by simp [x, hz, hAxis]
    refine ⟨x, Prod.ext (Subtype.ext ?_) ?_⟩
    · change boundaryFoot i x = (z : X n)
      rw [boundaryFoot_apply, hxi]
      change ((z : X n) - t • axis i) - (-t) • axis i = (z : X n)
      rw [neg_smul, sub_neg_eq_add, sub_add_cancel]
    · change -x i = t
      rw [hxi, neg_neg]
  exact ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hAij) (LinearMap.range_eq_top.mpr hAs)

variable [NeZero n] {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M]

end CalderonPatch
