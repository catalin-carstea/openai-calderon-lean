module

public import Proof.CalderonPatch.CoordinateMetricSection
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
public import Proof.CalderonPatch.NativeNormalChart
import Proof.CalderonN.MetricPullback
import Mathlib.Tactic.Ring
public import Proof.CalderonPatch.ReturnToOriginal
public import Proof.CalderonPatch.NativeBoundaryMetricChart
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Piecewise
public import Proof.CalderonN.Coordinates
public import Proof.CalderonPatch.BoundaryChartExtension
public import Proof.CalderonPatch.CapShift

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "TangentPlane" => boundaryTangentPlane (0 : I n)
local notation "H" => inwardHalfSpace n

/-- Restrict a product boundary chart to a smaller open signed domain. -/
@[expose] def ProductBoundaryChart.restrictAmbient
    (D : ProductBoundaryChart (n := n) (M := M) (Z := TangentPlane))
    {W : Set (TangentPlane × ℝ)} (hW : IsOpen W) (hWD : W ⊆ D.ambient) :
    ProductBoundaryChart (n := n) (M := M) (Z := TangentPlane) := by
  let c := D.coord
  let U := c.source ∩ c ⁻¹' W
  let V := W ∩ (univ ×ˢ Ici (0 : ℝ))
  have hV : V ⊆ c.target := D.target_eq.symm ▸ inter_subset_inter_left _ hWD
  let d : PartialEquiv M (TangentPlane × ℝ) :=
    { toFun := c
      invFun := c.symm
      source := U
      target := V
      map_source' := fun x hx => ⟨hx.2,(D.target_eq ▸ c.map_source hx.1 : _ ∈ D.ambient ∩ _).2⟩
      map_target' := fun x hx => ⟨c.map_target (hV hx), by
        change c (c.symm x) ∈ W
        rw [c.right_inv (hV hx)]
        exact hx.1⟩
      left_inv' := fun x hx => c.left_inv hx.1
      right_inv' := fun x hx => c.right_inv (hV hx) }
  have hU : IsOpen U := D.smooth.continuousOn.isOpen_inter_preimage D.open_source hW
  exact ⟨d,hU,W,hW,rfl,D.smooth.mono inter_subset_left,D.smooth_inverse.mono hV,
    fun x hx => D.interior_iff x hx.1⟩

end CalderonPatch
