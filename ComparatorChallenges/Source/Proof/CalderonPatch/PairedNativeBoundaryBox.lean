module

public import Proof.CalderonPatch.NativeBoundaryMetricChart
public import Proof.CalderonPatch.BoundaryChartTests
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates
public import Proof.CalderonPatch.BoundaryChartExtension
public import Proof.CalderonPatch.CapShift
public import Proof.CalderonPatch.Energy
public import Proof.CalderonPatch.NativeNormalChart

public section
noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ}
local notation "E" => X (n+1)
local notation "Y" => X n
local notation "J" => 𝓡∂ (n+1)
local notation "L" => (inwardChartSplit (n := n+1))
local notation "P" => boundaryTangentPlane (0 : I (n+1)) × ℝ

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

/-- The normal charts for the two metrics, with the product charts
used for cap attachment and one common coordinate half box used for
the measured boundary jets. -/
structure PairedNativeBoundaryBox (g₁ g₂ : SmoothMetric (n+1) M)
    (Γ : Set ((J).boundary M)) (p : (J).boundary M) where
  prod₁ : ProductBoundaryChart (n := n+1) (M := M) (Z := boundaryTangentPlane (0 : I (n+1)))
  prod₂ : ProductBoundaryChart (n := n+1) (M := M) (Z := boundaryTangentPlane (0 : I (n+1)))
  first : NativeBoundaryMetricChart g₁ p
  second : NativeBoundaryMetricChart g₂ p
  source₁ : first.coord.source = prod₁.coord.source
  source₂ : second.coord.source = prod₂.coord.source
  ambient₁ : first.ambient = L ⁻¹' prod₁.ambient
  ambient₂ : second.ambient = L ⁻¹' prod₂.ambient
  coord₁ : (first.coord : M → E) = (inwardChartSplit (n := n+1)).symm ∘ prod₁.coord
  coord₂ : (second.coord : M → E) = (inwardChartSplit (n := n+1)).symm ∘ prod₂.coord
  signed : Set E
  open_signed : IsOpen signed
  signed₁ : signed ⊆ first.ambient
  signed₂ : signed ⊆ second.ambient
  center_signed : second.coord p ∈ signed
  trace_first : ∀ q : (J).boundary M, (q : M) ∈ first.coord.source → first.coord q ∈ signed → q ∈ Γ
  trace_second : ∀ q : (J).boundary M, (q : M) ∈ second.coord.source → second.coord q ∈ signed →
    (q : M) ∈ first.coord.source ∧ first.coord q = second.coord q ∧ q ∈ Γ
  common_inverse : EqOn first.coord.symm second.coord.symm (signed ∩ {z | z 0 = 0})
  boxLower : I (n+1) → ℝ
  boxUpper : I (n+1) → ℝ
  bounds : boxLower ≤ boxUpper
  lower_zero : boxLower 0 = 0
  upper_pos : 0 < boxUpper 0
  center_box : normalTangentialCoordinates (second.coord p) ∈ tangentialBox boxLower boxUpper
  closed_box : MapsTo (WithLp.toLp 2) (Icc boxLower boxUpper) signed
  face_patch : MapsTo (first.coord.symm ∘ normalFacePoint) (tangentialBox boxLower boxUpper) (Subtype.val '' Γ)

end CalderonPatch
