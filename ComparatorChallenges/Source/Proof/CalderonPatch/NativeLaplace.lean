module

public import Proof.CalderonPatch.CoordinateMetric
public import Proof.CalderonN.MetricPullback
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Proof.CalderonN.Chart
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
import Proof.CalderonN.LinearMetric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
public import Proof.CalderonN.Coordinates
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import Proof.CalderonPatch.Energy

@[expose] public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (X laplace)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

theorem exists_smooth_interiorChart (p : M) (hp : p ∈ (𝓡∂ n).interior M) :
    ∃ e : OpenPartialHomeomorph M (X n), p ∈ e.source ∧
      ContMDiffOn J K ∞ e e.source ∧ ContMDiffOn K J ∞ e.symm e.target := sorry

/-- The scalar Laplace–Beltrami operator at interior points. The weak
interior kernel law uses its extension by zero at boundary points. -/
def nativeLaplace (g : SmoothMetric n M) (u : M → ℝ) (p : M) : ℝ :=
  open scoped Classical in
  if h : p ∈ (𝓡∂ n).interior M then
    let e := (exists_smooth_interiorChart p h).choose
    laplace (coordinateMetric g e) (u ∘ e.symm) (e p)
  else 0

end CalderonPatch
