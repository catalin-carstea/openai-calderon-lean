module

public import Proof.CalderonPatch.VerticalCap
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
public import Proof.CalderonN.Coordinates
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Geometry.Manifold.ContMDiff.Basic

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, Z × ℝ)

/-- A boundary chart written as a relatively open subset of a product
half space, with inward height in its second coordinate. -/
structure ProductBoundaryChart where
  coord : PartialEquiv M (Z × ℝ)
  open_source : IsOpen coord.source
  ambient : Set (Z × ℝ)
  open_ambient : IsOpen ambient
  target_eq : coord.target = ambient ∩ (univ ×ˢ Ici (0 : ℝ))
  smooth : ContMDiffOn J K ∞ coord coord.source
  smooth_inverse : ContMDiffOn K J ∞ coord.symm coord.target
  interior_iff : ∀ x ∈ coord.source, x ∈ (J).interior M ↔ 0 < (coord x).2

/-- The geometry of an attached cap before a metric is pasted into the
new region. The extension has the same underlying manifold type, with
the original embedded inward via a map supported in one chart. -/
structure CapShift (D : ProductBoundaryChart (n := n) (M := M) (Z := Z)) where
  embed : M → M
  inverse : M → M
  cap : Set M
  support : Set M
  closed_support : IsClosed support
  support_in_chart : support ⊆ D.coord.source
  embed_eq_id_off_support : EqOn embed id supportᶜ
  cap_closure_in_support : closure cap ⊆ support
  left_inv : Function.LeftInverse inverse embed
  smooth : ContMDiff J J ∞ embed
  smooth_inverse : ContMDiffOn J J ∞ inverse (range embed)
  open_cap : IsOpen cap
  connected_cap : IsConnected cap
  cap_interior : cap ⊆ (J).interior M
  interior_image : embed '' (J).interior M = (J).interior M \ closure cap
  coordinateShift : (Z × ℝ) ≃ (Z × ℝ)
  smooth_coordinateShift : ContDiff ℝ ∞ coordinateShift
  smooth_coordinateShift_inverse : ContDiff ℝ ∞ coordinateShift.symm
  coordinateShift_spec : ∀ x ∈ D.coord.source,
    embed x ∈ D.coord.source ∧ D.coord (embed x) = coordinateShift (D.coord x)
  coordinateShift_ambient : ∀ q, coordinateShift q ∈ D.ambient ↔ q ∈ D.ambient
  capHeight : Z → ℝ
  smooth_capHeight : ContDiff ℝ ∞ capHeight
  cap_eq : cap = D.coord.symm '' pushedCap capHeight

end CalderonPatch
