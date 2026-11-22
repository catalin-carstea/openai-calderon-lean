module

public import Proof.Manuscript.ScalarConductivityDefs

import Proof.Manuscript.LocalExtensions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology

namespace CalderonPaper

open CalderonN (X)

variable {n : ℕ} [NeZero n] {Ω : Set (X n)}
  [ChartedSpace (EuclideanHalfSpace n) ↥(closure Ω)]
  [IsManifold (𝓡∂ n) ∞ ↥(closure Ω)]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

namespace EuclideanClosure

theorem continuous_boundaryCoordinate (D : EuclideanClosure Ω) (hΩ : IsOpen Ω) :
    Continuous (D.boundaryCoordinate hΩ) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem surjective_boundaryCoordinate (D : EuclideanClosure Ω) (hΩ : IsOpen Ω) :
    Function.Surjective (D.boundaryCoordinate hΩ) := by
  intro y
  let x : ↥(closure Ω) := ⟨y.val, y.property.1⟩
  have hx : x ∈ (J).boundary ↥(closure Ω) := (D.boundary_iff hΩ x).mpr y.property
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

def frontierCoordinate (D : EuclideanClosure Ω) (hΩ : IsOpen Ω) :
    ↥(frontier Ω) → ↥((J).boundary ↥(closure Ω)) :=
  fun p => ⟨⟨p.val, p.property.1⟩, (D.boundary_iff hΩ _).mpr p.property⟩

theorem continuous_frontierCoordinate (D : EuclideanClosure Ω) (hΩ : IsOpen Ω) :
    Continuous (D.frontierCoordinate hΩ) :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem frontierCoordinate_boundaryCoordinate (D : EuclideanClosure Ω) (hΩ : IsOpen Ω)
    (p : ↥((J).boundary ↥(closure Ω))) :
    D.frontierCoordinate hΩ (D.boundaryCoordinate hΩ p) = p :=
  Subtype.ext (Subtype.ext rfl)

theorem contMDiff_restrict (D : EuclideanClosure Ω) {g : X n → ℝ}
    (hg : SmoothThrough (closure Ω) g) :
    ContMDiff J R ∞ (g ∘ (Subtype.val : ↥(closure Ω) → X n)) := by
  intro x
  obtain ⟨U, hU, hx, G, hG, hEq⟩ := hg x.val x.property
  have hG' : ContMDiffAt K R ∞ G x.val :=
    contMDiffAt_iff_contDiffAt.mpr (hG.contDiffAt (hU.mem_nhds hx))
  have h := hG'.comp x (D.inclusion_smooth x)
  have he : (G ∘ (Subtype.val : ↥(closure Ω) → X n)) =ᶠ[𝓝 x]
      (g ∘ Subtype.val) := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)] with y hy
    exact hEq ⟨hy, y.property⟩
  exact h.congr_of_eventuallyEq he.symm

end EuclideanClosure

/-- The total ambient representative of a self-map of the Euclidean closure.
Values outside the closure are irrelevant. -/
def closureSelfMap (Φ : ↥(closure Ω) → ↥(closure Ω)) (x : X n) : X n := by
  classical
  exact if h : x ∈ closure Ω then (Φ ⟨x, h⟩ : X n) else x

theorem closureSelfMap_on_closure (Φ : ↥(closure Ω) → ↥(closure Ω)) (x : ↥(closure Ω)) :
    closureSelfMap Φ x = (Φ x : X n) := by simp [closureSelfMap, x.property]

theorem closureSelfMap_mapsTo (Φ : ↥(closure Ω) → ↥(closure Ω)) :
    MapsTo (closureSelfMap Φ) (closure Ω) (closure Ω) := by
  intro x hx
  rw [show closureSelfMap Φ x = (Φ ⟨x, hx⟩ : X n) by simp [closureSelfMap, hx]]
  exact (Φ ⟨x, hx⟩).property

theorem closureSelfMap_continuousOn (Φ : ↥(closure Ω) → ↥(closure Ω))
    (hΦ : Continuous Φ) : ContinuousOn (closureSelfMap Φ) (closure Ω) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (closure Ω).domRestrict (closureSelfMap Φ) = Subtype.val ∘ Φ :=
    funext (closureSelfMap_on_closure Φ)
  rw [he]
  exact continuous_subtype_val.comp hΦ

namespace EuclideanClosure

theorem closureSelfMap_smooth_on_interior (D : EuclideanClosure Ω)
    (Φ : ↥(closure Ω) → ↥(closure Ω)) (hΦ : ContMDiff J J ∞ Φ) :
    ContDiffOn ℝ ∞ (closureSelfMap Φ) Ω := by
  apply contMDiffOn_iff_contDiffOn.mp
  refine ((D.inclusion_smooth.comp hΦ).comp_contMDiffOn D.interiorInverse_smooth).congr ?_
  intro x hx
  change closureSelfMap Φ x = (Φ (D.interiorInverse x) : X n)
  calc
    _ = closureSelfMap Φ (D.interiorInverse x : X n) :=
      congrArg (closureSelfMap Φ) (D.interiorInverse_apply x hx).symm
    _ = _ := closureSelfMap_on_closure Φ (D.interiorInverse x)

theorem closureSelfMap_mapsTo_interior (D : EuclideanClosure Ω)
    (Φ : ↥(closure Ω) ≃ₘ⟮J, J⟯ ↥(closure Ω)) :
    MapsTo (closureSelfMap Φ) Ω Ω := by
  intro x hx
  let p : ↥(closure Ω) := ⟨x, subset_closure hx⟩
  have hp : (J).IsInteriorPoint p := (D.interior_iff p).mpr hx
  have hΦp : (J).IsInteriorPoint (Φ p) := ((Φ.isLocalDiffeomorph p).isInteriorPoint_iff (by simp)).mp hp
  change closureSelfMap Φ (p : X n) ∈ Ω
  rw [closureSelfMap_on_closure]
  exact (D.interior_iff (Φ p)).mp hΦp

end EuclideanClosure

/-- A positive scalar conductivity contributes half its logarithmic metric exponent. -/
def conductivityExponent (n : ℕ) (γ : X n → ℝ) (x : X n) : ℝ :=
  Real.log (γ x) / ((n : ℝ) - 2)

theorem smoothThrough_conductivityExponent {γ : X n → ℝ}
    (hγ : SmoothThrough (closure Ω) γ) (hpos : ∀ x ∈ closure Ω, 0 < γ x) :
    SmoothThrough (closure Ω) (conductivityExponent n γ) := by
  intro x hx
  obtain ⟨U, hU, hxU, G, hG, hEq⟩ := hγ x hx
  let V := U ∩ G ⁻¹' Ioi (0 : ℝ)
  have hV : IsOpen V := hG.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hxV : x ∈ V := ⟨hxU, show 0 < G x by rw [hEq ⟨hxU, hx⟩]; exact hpos x hx⟩
  refine ⟨V, hV, hxV, fun y => Real.log (G y) / ((n : ℝ) - 2), ?_, ?_⟩
  · exact ((hG.mono inter_subset_left).log (fun y hy => (show 0 < G y from hy.2).ne')).div_const _
  · intro y hy
    simp only [conductivityExponent, hEq ⟨hy.1.1, hy.2⟩]

end CalderonPaper
