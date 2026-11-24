module

public import Proof.CalderonPatch.NativeNormalChart
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates
public import Proof.CalderonPatch.BoundaryChartExtension

public section
noncomputable section
open Metric Set
open scoped Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} [NeZero n]
local notation "L" => (inwardChartSplit (n := n))
local notation "Z" => boundaryTangentPlane (0 : I n)

/-- A signed coordinate box containing the complete support of the
vertical push, strictly inside its faces. -/
structure SignedCapBox (W : Set (Z × ℝ)) (z : Z) where
  lower : I n → ℝ
  upper : I n → ℝ
  bounds : lower ≤ upper
  radius : ℝ
  radius_pos : 0 < radius
  bottom_lt : lower 0 < -radius
  top_lt : radius < upper 0
  box_inside : MapsTo (L ∘ WithLp.toLp 2) (Icc lower upper) W
  push_inside : MapsTo (WithLp.ofLp ∘ (inwardChartSplit (n := n)).symm)
    (closedBall z radius ×ˢ Icc (-radius) radius)
    (Set.pi univ fun i => Ioo (lower i) (upper i))

end CalderonPatch
