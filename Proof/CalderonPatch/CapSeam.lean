module

public import Proof.CalderonPatch.CapShift

public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

local notation "J" => 𝓡∂ n

omit [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z] in
/-- The graph of a positive cap height is a limit of cap points
on the vertical segment over the same tangential point. -/
theorem mem_closure_pushedCap_of_pos {b : Z → ℝ} {z : Z} (hz : 0 < b z) :
    (z, b z) ∈ closure (pushedCap b) := by
  have hI : b z ∈ closure (Ioo 0 (b z)) := by rw [closure_Ioo hz.ne]; exact ⟨hz.le, le_rfl⟩
  have hc : Continuous (fun t : ℝ => (z, t)) := continuous_const.prodMk continuous_id
  have hsub : (fun t : ℝ => (z, t)) '' Ioo 0 (b z) ⊆ pushedCap b := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht
  exact closure_mono hsub (image_closure_subset_closure_image hc (mem_image_of_mem _ hI))

/-- A continued cap identification agrees at every covered point of
the original seam where the two charts give the same boundary coordinate. -/
theorem eq_on_capSeam_of_eq_on_pushedCap
    {D₁ D₂ : ProductBoundaryChart (n := n) (M := M) (Z := Z)}
    (C₁ : CapShift D₁) (C₂ : CapShift D₂) {b : Z → ℝ} {z : Z}
    (hHeight : 0 < b z)
    (hGraph₁ : C₁.coordinateShift (z, 0) = (z, b z))
    (hGraph₂ : C₂.coordinateShift (z, 0) = (z, b z))
    (hCap₁ : pushedCap b ⊆ D₁.coord.target) (hCap₂ : pushedCap b ⊆ D₂.coord.target)
    {p : M} (hp₁ : p ∈ D₁.coord.source) (hp₂ : p ∈ D₂.coord.source)
    (hq₁ : D₁.coord p = (z, 0)) (hq₂ : D₂.coord p = (z, 0))
    (e : OpenPartialHomeomorph M M) (hs : e.source = (J).interior M)
    (hCap : EqOn (e ∘ D₂.coord.symm) D₁.coord.symm (pushedCap b)) :
    C₂.embed p ∈ e.source ∧ e (C₂.embed p) = C₁.embed p := by
  obtain ⟨hs₁, hd₁⟩ := C₁.coordinateShift_spec p hp₁
  obtain ⟨hs₂, hd₂⟩ := C₂.coordinateShift_spec p hp₂
  rw [hq₁,hGraph₁] at hd₁
  rw [hq₂,hGraph₂] at hd₂
  set q : Z × ℝ := (z, b z)
  have hT₁ : q ∈ D₁.coord.target := hd₁ ▸ D₁.coord.map_source hs₁
  have hT₂ : q ∈ D₂.coord.target := hd₂ ▸ D₂.coord.map_source hs₂
  have hQ₁ : D₁.coord.symm q = C₁.embed p := by rw [← hd₁, D₁.coord.left_inv hs₁]
  have hQ₂ : D₂.coord.symm q = C₂.embed p := by rw [← hd₂, D₂.coord.left_inv hs₂]
  let U := D₁.coord.target ∩ D₂.coord.target ∩ {x : Z × ℝ | 0 < x.2}
  have hTo : MapsTo D₂.coord.symm U e.source := by
    intro x hx
    rw [hs, D₂.interior_iff _ (D₂.coord.map_target hx.1.2), D₂.coord.right_inv hx.1.2]
    exact hx.2
  have hqU : q ∈ U := ⟨⟨hT₁,hT₂⟩,hHeight⟩
  have hEU : pushedCap b ⊆ U := fun x hx => ⟨⟨hCap₁ hx,hCap₂ hx⟩,hx.1⟩
  refine ⟨hQ₂ ▸ hTo hqU, ?_⟩
  have hc₂ := e.continuousOn.comp (D₂.smooth_inverse.continuousOn.mono fun _ hx => hx.1.2) hTo
  have hc₁ := D₁.smooth_inverse.continuousOn.mono (show U ⊆ D₁.coord.target from fun _ hx => hx.1.1)
  let V := U ∩ closure (pushedCap b)
  have hEV : pushedCap b ⊆ V := fun x hx => ⟨hEU hx, subset_closure hx⟩
  have hV : V ⊆ U := inter_subset_left
  have hVcl : V ⊆ closure (pushedCap b) := inter_subset_right
  have hqV : q ∈ V := ⟨hqU, mem_closure_pushedCap_of_pos hHeight⟩
  have heq := hCap.of_subset_closure (hc₂.mono hV) (hc₁.mono hV) hEV hVcl hqV
  simpa only [Function.comp_apply, hQ₁, hQ₂] using heq

end CalderonPatch
