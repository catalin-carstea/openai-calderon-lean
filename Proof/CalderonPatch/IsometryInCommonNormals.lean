module

public import Proof.CalderonPatch.BoundaryCoordinateIsometry

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "H" => inwardHalfSpace n
local notation "Pos" => positiveHalfSpace n

/-- A smooth isometry fixing an open boundary patch preserves paired
normal coordinates with the same boundary parametrization. -/
theorem eventually_eq_in_commonNormalCoordinates {g₁ g₂ : SmoothMetric n M}
    (Φ : M ≃ₘ⟮J, J⟯ M) (hΦ : PullbackMetric g₁ g₂ Φ)
    {p : M} (D₁ : NativeBoundaryMetricChart g₁ p) (D₂ : NativeBoundaryMetricChart g₂ p)
    {V : Set M} (hV : IsOpen V) (hpV : p ∈ V) (hpB : p ∈ (𝓡∂ n).boundary M)
    (hFix : EqOn Φ id (V ∩ (𝓡∂ n).boundary M)) (hCoords : EqOn D₁.coord D₂.coord (V ∩ (𝓡∂ n).boundary M)) :
    (D₁.coord ∘ Φ ∘ D₂.coord.symm) =ᶠ[𝓝[H] (D₂.coord p)] id := by
  let T := (J).interior M
  let f := Φ.toHomeomorph
  let e₀ := f.toOpenPartialHomeomorph
  let e := e₀.restr T
  have hTo : IsOpen T := (J).isOpen_interior (n := ∞) (by simp)
  have hs : e.source = T := by rw [e₀.restr_source' T hTo]; simp [e₀]
  have ht : e.target = T := by
    rw [← e.image_source_eq_target, hs]
    exact Φ.image_interior (by simp)
  have he : IsLocalMetricIsometry g₁ g₂ e := ⟨Φ.contMDiff.contMDiffOn,
    Φ.symm.contMDiff.contMDiffOn, fun x _ => hΦ x⟩
  have hpF : f p = p := hFix ⟨hpV,hpB⟩
  have hpF' : f.symm p = p := by conv_lhs => rw [← hpF, f.symm_apply_apply]
  let x := D₂.coord p
  let y := D₁.coord p
  let a : X n → X n := D₁.coord ∘ f ∘ D₂.coord.symm
  let b : X n → X n := D₂.coord ∘ f.symm ∘ D₁.coord.symm
  obtain ⟨U₂,hU₂,hx,hU₂D,hTo₂,hC₂,hF₂,hM₂,hFace₂,hMet₂⟩ :=
    exists_boundaryCoordinateIsometry he hs ht (fun _ _ => rfl) D₂ D₁ hpF
  obtain ⟨U₁,hU₁,hy,hU₁D,_,hC₁,hF₁,hM₁,hFace₁,hMet₁⟩ :=
    exists_boundaryCoordinateIsometry he.symm ht hs (fun _ _ => rfl) D₁ D₂ hpF'
  have hUH : U₂ ∩ H ⊆ D₂.coord.target := fun z hz => D₂.target_eq.symm ▸ ⟨hU₂D hz.1,hz.2⟩
  have hxy : a x = y := by
    change D₁.coord (f (D₂.coord.symm (D₂.coord p))) = D₁.coord p
    rw [D₂.coord.left_inv D₂.point_source, hpF]
  have hAH : MapsTo a (U₂ ∩ H) H := fun z hz =>
    (D₁.target_eq ▸ D₁.coord.map_source (hTo₂ hz) : a z ∈ D₁.ambient ∩ H).2
  have hBcomp : (b ∘ a) =ᶠ[𝓝[H] x] id := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU₂.mem_nhds hx), self_mem_nhdsWithin] with z hz hh
    change D₂.coord (f.symm (D₁.coord.symm (D₁.coord (f (D₂.coord.symm z))))) = z
    have h := hTo₂ ⟨hz,hh⟩
    change f (D₂.coord.symm z) ∈ D₁.coord.source at h
    rw [D₁.coord.left_inv h, f.symm_apply_apply, D₂.coord.right_inv (hUH ⟨hz,hh⟩)]
  have hxH : x ∈ H := (mem_inwardHalfSpace).mpr (D₂.point_face.ge)
  have hNhds : 𝓝[U₂ ∩ H] x = 𝓝[H] x :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hU₂.mem_nhds hx))
  have hAt : Tendsto a (𝓝[H] x) (𝓝[H] (a x)) := by
    rw [← hNhds]
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hC₂ x ⟨hx,hxH⟩).tendsto (Filter.mem_of_superset self_mem_nhdsWithin hAH)
  have hLe₂ := eventually_normalHeight_le_of_local_isometry D₂.point_face hU₂ hx
    (fun z hz => D₂.normal_field z (hU₂D hz)) D₁.normal_field D₁.smooth_field.2
    hF₂ hC₂ hM₂ hFace₂ hMet₂
  have hLe₁ := eventually_normalHeight_le_of_local_isometry D₁.point_face hU₁ hy
    (fun z hz => D₁.normal_field z (hU₁D hz)) D₂.normal_field D₂.smooth_field.2
    hF₁ hC₁ hM₁ hFace₁ hMet₁
  have hLe : ∀ᶠ z in 𝓝[H] (a x), b z 0 ≤ z 0 := hxy.symm ▸ hLe₁
  have hHeight := eventually_normalHeight_eq_of_inverse_comparison hAt hBcomp hLe₂ hLe
  have hXV : D₂.coord.symm x ∈ V := by
    change D₂.coord.symm (D₂.coord p) ∈ V
    rwa [D₂.coord.left_inv D₂.point_source]
  have hNear : ∀ᶠ z in 𝓝[D₂.coord.target] x, D₂.coord.symm z ∈ V :=
    (D₂.smooth_inverse.continuousOn x (D₂.coord.map_source D₂.point_source)).eventually_mem (hV.mem_nhds hXV)
  obtain ⟨W,hWMap,hW,hxW⟩ := _root_.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hNear)
  let U := U₂ ∩ W
  have hU : IsOpen U := hU₂.inter hW
  have hxU : x ∈ U := ⟨hx,hxW⟩
  have hSub {S : Set (X n)} : U ∩ S ⊆ U₂ ∩ S := fun _ hz => ⟨hz.1.1,hz.2⟩
  have hId : EqOn a id (U ∩ {z | z (0 : I n) = 0}) := by
    intro z hz
    have hzH : z ∈ H := (mem_inwardHalfSpace).mpr hz.2.ge
    have hzT := hUH ⟨hz.1.1,hzH⟩
    have hzV : D₂.coord.symm z ∈ V := hWMap z hz.1.2 hzT
    have hzB : D₂.coord.symm z ∈ (𝓡∂ n).boundary M := by
      rw [← (J).compl_interior]
      intro hzI
      have hPos := (D₂.interior_iff _ (D₂.coord.map_target hzT)).mp hzI
      rw [D₂.coord.right_inv hzT] at hPos
      exact ((mem_positiveHalfSpace).mp hPos).ne' hz.2
    change D₁.coord (Φ (D₂.coord.symm z)) = z
    rw [hFix ⟨hzV,hzB⟩]
    exact (hCoords ⟨hzV,hzB⟩).trans (D₂.coord.right_inv hzT)
  exact eventually_eq_id_of_normalHeight_eq_and_fixes_face D₂.point_face hU hxU
    (fun z hz => D₂.normal_field z (hU₂D hz.1)) D₁.normal_field D₁.smooth_field.2
    (hF₂.mono hSub) (hC₂.mono hSub) (hM₂.mono_left hSub) hId hHeight
    (fun z hz => hMet₂ z (hSub hz))

end CalderonPatch
