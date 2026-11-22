module

public import Proof.CalderonPatch.BoundaryChartTests

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (X I)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "J" => 𝓡∂ (n+1)
local notation "R" => 𝓘(ℝ, ℝ)
local notation "Z" => X (n+1)
local notation "H" => inwardHalfSpace (n+1)

/-- A shared signed neighborhood reads as the same ambient face in
both charts. Two trials there may have different interior profiles. -/
theorem eqOn_boundaryChartTests_of_common_face
    {g₁ g₂ : SmoothMetric (n+1) M} {p₁ p₂ : M}
    (D₁ : NativeBoundaryMetricChart g₁ p₁) (D₂ : NativeBoundaryMetricChart g₂ p₂)
    {U : Set Z} (hU₁ : U ⊆ D₁.ambient) (hU₂ : U ⊆ D₂.ambient)
    {f₁ f₂ : Z → ℝ} (hf₁ : HasCompactSupport f₁) (hf₂ : HasCompactSupport f₂)
    (hS₁ : tsupport f₁ ∩ H ⊆ U) (hS₂ : tsupport f₂ ∩ H ⊆ U)
    (hChart : EqOn D₁.coord.symm D₂.coord.symm (U ∩ {z | z 0 = 0}))
    (hFace : EqOn f₁ f₂ (U ∩ {z | z 0 = 0})) :
    EqOn (boundaryChartTest D₁ f₁) (boundaryChartTest D₂ f₂) ((J).boundary M) := by
  have hT₁ : U ∩ H ⊆ D₁.coord.target := by
    rw [D₁.target_eq]
    exact inter_subset_inter_left _ hU₁
  have hT₂ : U ∩ H ⊆ D₂.coord.target := by
    rw [D₂.target_eq]
    exact inter_subset_inter_left _ hU₂
  have hSupport₁ := tsupport_boundaryChartTest_subset D₁ hf₁
    (fun z hz => hT₁ ⟨hS₁ hz,hz.2⟩)
  have hSupport₂ := tsupport_boundaryChartTest_subset D₂ hf₂
    (fun z hz => hT₂ ⟨hS₂ hz,hz.2⟩)
  have hAt (z : Z) (hz : z ∈ U ∩ {z | z 0 = 0}) :
      boundaryChartTest D₁ f₁ (D₁.coord.symm z) =
        boundaryChartTest D₂ f₂ (D₁.coord.symm z) := by
    have hPos := mem_inwardHalfSpace.mpr (show z 0 = 0 from hz.2).ge
    calc
      _ = f₁ z := boundaryChartTest_comp_inverse D₁ f₁ (hT₁ ⟨hz.1,hPos⟩)
      _ = f₂ z := hFace hz
      _ = boundaryChartTest D₂ f₂ (D₂.coord.symm z) :=
        (boundaryChartTest_comp_inverse D₂ f₂ (hT₂ ⟨hz.1,hPos⟩)).symm
      _ = _ := congrArg (boundaryChartTest D₂ f₂) (hChart hz).symm
  intro x hx
  by_cases h₁ : x ∈ tsupport (boundaryChartTest D₁ f₁)
  · obtain ⟨z,hz,rfl⟩ := hSupport₁ h₁
    have hT := hT₁ ⟨hS₁ hz,hz.2⟩
    have h0 := D₁.coord_height_eq_zero (D₁.coord.map_target hT) hx
    rw [D₁.coord.right_inv hT] at h0
    exact hAt z ⟨hS₁ hz,h0⟩
  by_cases h₂ : x ∈ tsupport (boundaryChartTest D₂ f₂)
  · obtain ⟨z,hz,rfl⟩ := hSupport₂ h₂
    have hT := hT₂ ⟨hS₂ hz,hz.2⟩
    have h0 := D₂.coord_height_eq_zero (D₂.coord.map_target hT) hx
    rw [D₂.coord.right_inv hT] at h0
    have hZ : z ∈ U ∩ {z | z 0 = 0} := ⟨hS₂ hz,h0⟩
    rw [← hChart hZ]
    exact hAt z hZ
  exact (image_eq_zero_of_notMem_tsupport h₁).trans (image_eq_zero_of_notMem_tsupport h₂).symm

/-- A half-box supported trial induces a trace whose support lies
within the measured patch if the bottom face lies within the patch. -/
theorem tsupport_boundaryChartTest_trace_subset
    {g : SmoothMetric (n+1) M} {p : M} (D : NativeBoundaryMetricChart g p)
    {l r : I (n+1) → ℝ} (hl0 : l 0 = 0)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) D.ambient)
    {f : Z → ℝ} (hf : HasCompactSupport f)
    (hS : tsupport f ∩ H ⊆ normalHalfBox l r)
    {Γ : Set ((J).boundary M)}
    (hΓ : MapsTo (D.coord.symm ∘ normalFacePoint) (tangentialBox l r) (Subtype.val '' Γ)) :
    tsupport (fun x : (J).boundary M => boundaryChartTest D f x) ⊆ Γ := by
  let u := boundaryChartTest D f
  have hIncl : tsupport (fun x : (J).boundary M => u x) ⊆ Subtype.val ⁻¹' tsupport u := by
    apply closure_minimal _ ((isClosed_tsupport u).preimage continuous_subtype_val)
    intro x hx
    exact subset_closure (show (x : M) ∈ Function.support u from hx)
  intro x hx
  have hxD := tsupport_boundaryChartTest_subset_halfBox D hl0 hBox hf hS (hIncl hx)
  let y := normalTangentialCoordinates (D.coord x)
  have hy : y ∈ tangentialBox l r := fun i =>
    ⟨hxD.2.2.2 _ (Fin.succAbove_ne _ _), hxD.2.2.1 _⟩
  have h := hΓ hy
  change D.coord.symm (normalFacePoint (normalTangentialCoordinates (D.coord x))) ∈ _ at h
  rw [normalFacePoint_tangentialCoordinates (D.coord_height_eq_zero hxD.1 x.property),
    D.coord.left_inv hxD.1] at h
  obtain ⟨x',hx',he⟩ := h
  exact (Subtype.ext he : x' = x) ▸ hx'

end CalderonPatch
