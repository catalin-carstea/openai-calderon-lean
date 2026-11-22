module

public import Proof.CalderonPatch.BoundaryCoordinateIsometry
public import Proof.CalderonPatch.CompletedMetric

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace (EuclideanHalfSpace n) M₁]
  [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace (EuclideanHalfSpace n) M₂]
  [IsManifold (𝓡∂ n) ∞ M₁] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "H" => inwardHalfSpace n
local notation "P" => positiveHalfSpace n

/-- A continuous extension of an interior metric isometry and its
inverse are smooth up to the boundary. In signed normal coordinates
the two map inequalities give height preservation, so the remaining
coordinates are taken on an interior slice. -/
theorem contMDiff_of_interiorIsometry_homeomorph
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e)
    (hs : e.source = (J).interior M₂) (ht : e.target = (J).interior M₁)
    (f : M₂ ≃ₜ M₁) (hf : EqOn f e e.source) (hfi : EqOn f.symm e.symm e.target) :
    ContMDiff J J ∞ f := by
  intro p
  by_cases hp : p ∈ e.source
  · exact (he.smooth.congr hf).contMDiffAt (e.open_source.mem_nhds hp)
  have hpB : p ∈ (J).boundary M₂ := by
    rw [← (J).compl_interior, ← hs]
    exact hp
  have hqB : f p ∈ (J).boundary M₁ := by
    rw [← (J).compl_interior]
    intro hq
    rw [← interiorIsometry_homeomorph_image hs ht hf] at hq
    obtain ⟨p',hp',h⟩ := hq
    exact hp (hs.symm ▸ (f.injective h ▸ hp'))
  obtain ⟨D₂⟩ := exists_nativeBoundaryMetricChart g₂ p hpB
  obtain ⟨D₁⟩ := exists_nativeBoundaryMetricChart g₁ (f p) hqB
  let w := D₂.coord p
  let z := D₁.coord (f p)
  let a : X n → X n := D₁.coord ∘ f ∘ D₂.coord.symm
  let b : X n → X n := D₂.coord ∘ f.symm ∘ D₁.coord.symm
  obtain ⟨U₂,hU₂,hw,hU₂D,hMap₂,hC₂,hF₂,hM₂,hFace₂,hMet₂⟩ :=
    exists_boundaryCoordinateIsometry he hs ht hf D₂ D₁ rfl
  obtain ⟨U₁,hU₁,hz,hU₁D,hMap₁,hC₁,hF₁,hM₁,hFace₁,hMet₁⟩ :=
    exists_boundaryCoordinateIsometry he.symm ht hs hfi D₁ D₂ (f.symm_apply_apply p)
  have haz : a w = z := by
    change D₁.coord (f (D₂.coord.symm (D₂.coord p))) = D₁.coord (f p)
    rw [D₂.coord.left_inv D₂.point_source]
  have hAw : MapsTo a (U₂ ∩ H) H := by
    intro x hx
    exact (D₁.target_eq ▸ D₁.coord.map_source (hMap₂ hx) : a x ∈ D₁.ambient ∩ H).2
  have hBw : ∀ᶠ x in 𝓝[H] w, (b ∘ a) x = id x := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU₂.mem_nhds hw), self_mem_nhdsWithin] with x hU hH
    have hT : x ∈ D₂.coord.target := D₂.target_eq.symm ▸ ⟨hU₂D hU,hH⟩
    have hS : f (D₂.coord.symm x) ∈ D₁.coord.source := hMap₂ ⟨hU,hH⟩
    change D₂.coord (f.symm (D₁.coord.symm (D₁.coord (f (D₂.coord.symm x))))) = x
    rw [D₁.coord.left_inv hS, f.symm_apply_apply, D₂.coord.right_inv hT]
  have hwH : w ∈ H := (mem_inwardHalfSpace).mpr (by change 0 ≤ D₂.coord p 0; rw [D₂.point_face])
  have hAwT : Tendsto a (𝓝[H] w) (𝓝[H] (a w)) := by
    have hh : 𝓝[U₂ ∩ H] w = 𝓝[H] w := nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hU₂.mem_nhds hw))
    rw [← hh]
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hC₂ w ⟨hw,hwH⟩).tendsto (Filter.mem_of_superset self_mem_nhdsWithin hAw)
  have hLe₂ := eventually_normalHeight_le_of_local_isometry D₂.point_face hU₂ hw
    (fun x hx => D₂.normal_field x (hU₂D hx)) D₁.normal_field D₁.smooth_field.2
    hF₂ hC₂ hM₂ hFace₂ hMet₂
  have hLe₁ := eventually_normalHeight_le_of_local_isometry D₁.point_face hU₁ hz
    (fun x hx => D₁.normal_field x (hU₁D hx)) D₂.normal_field D₂.smooth_field.2
    hF₁ hC₁ hM₁ hFace₁ hMet₁
  have hLeInv : ∀ᶠ y in 𝓝[H] (a w), b y 0 ≤ y 0 := by
    rw [haz]
    exact hLe₁
  have hHeight := eventually_normalHeight_eq_of_inverse_comparison hAwT hBw hLe₂ hLeInv
  obtain ⟨A,hA,hAeq⟩ := exists_smooth_boundaryGerm_of_local_isometry
    D₂.point_face hU₂ hw (fun x hx => D₂.normal_field x (hU₂D hx)) D₁.normal_field
    D₁.smooth_field.2 hF₂ hC₂ hM₂ hHeight hMet₂
  have hTc : Tendsto (D₂.coord : M₂ → X n) (𝓝 p) (𝓝[H] w) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (D₂.smooth.continuousOn.continuousAt (D₂.open_source.mem_nhds D₂.point_source)).tendsto
    filter_upwards [D₂.open_source.mem_nhds D₂.point_source] with x hx
    exact (D₂.target_eq ▸ D₂.coord.map_source hx : _ ∈ D₂.ambient ∩ H).2
  have hAE : ∀ᶠ x in 𝓝 p, a (D₂.coord x) = A (D₂.coord x) := hTc.eventually hAeq
  have hSource : ∀ᶠ x in 𝓝 p, x ∈ D₂.coord.source := D₂.open_source.mem_nhds D₂.point_source
  have hReady : ∀ᶠ x in 𝓝 p, x ∈ D₂.coord.source ∧ f x ∈ D₁.coord.source :=
    hSource.and (f.continuous.continuousAt.eventually_mem (D₁.open_source.mem_nhds D₁.point_source))
  have hReady' : ∀ᶠ x in 𝓝 p, A (D₂.coord x) = D₁.coord (f x) ∧ f x ∈ D₁.coord.source := by
    filter_upwards [hReady,hAE] with x hx heq
    have hh : a (D₂.coord x) = D₁.coord (f x) := by
      change D₁.coord (f (D₂.coord.symm (D₂.coord x))) = _
      rw [D₂.coord.left_inv hx.1]
    exact ⟨heq.symm.trans hh,hx.2⟩
  obtain ⟨W,hW,hWo,hWp⟩ := _root_.eventually_nhds_iff.mp hReady'
  let F := A ∘ D₂.coord
  have hF : ContMDiffAt J K ∞ F p :=
    hA.contMDiffAt.comp p (D₂.smooth.contMDiffAt (D₂.open_source.mem_nhds D₂.point_source))
  have hFW : MapsTo F W D₁.coord.target := by
    intro x hx
    change A (D₂.coord x) ∈ D₁.coord.target
    rw [(hW x hx).1]
    exact D₁.coord.map_source (hW x hx).2
  have hSmooth : ContMDiffAt J J ∞ (D₁.coord.symm ∘ F) p :=
    ((D₁.smooth_inverse (F p) (hFW hWp)).comp p hF.contMDiffWithinAt hFW).contMDiffAt
      (hWo.mem_nhds hWp)
  apply hSmooth.congr_of_eventuallyEq
  filter_upwards [hWo.mem_nhds hWp] with x hx
  change f x = D₁.coord.symm (A (D₂.coord x))
  rw [(hW x hx).1, D₁.coord.left_inv (hW x hx).2]

variable [CompactSpace M₁] [CompactSpace M₂]

/-- The global interior isometry of compact manifolds with boundary
extends to a smooth metric isometry of the completed manifolds. -/
theorem smoothCompletion_of_interiorIsometry
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e)
    (hs : e.source = (J).interior M₂) (ht : e.target = (J).interior M₁) :
    ∃ f : M₂ ≃ₘ⟮J, J⟯ M₁, EqOn f e e.source ∧
      ∀ p (v w : TangentSpace J p), g₂.inner p v w =
        g₁.inner (f p) (mfderiv J J f p v) (mfderiv J J f p w) := by
  obtain ⟨f,hf,hfi⟩ := interiorIsometry_extends_homeomorph he hs ht
  have hF := contMDiff_of_interiorIsometry_homeomorph he hs ht f hf hfi
  have hFi := contMDiff_of_interiorIsometry_homeomorph he.symm ht hs f.symm hfi hf
  let Φ : M₂ ≃ₘ⟮J, J⟯ M₁ :=
    { f.toEquiv with contMDiff_toFun := hF, contMDiff_invFun := hFi }
  exact ⟨Φ,hf,pullbackMetric_of_interior_agreement he hs hF hf⟩

end CalderonPatch
