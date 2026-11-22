module

public import Proof.CalderonPatch.NativeBoundaryMetricChart
public import Proof.CalderonPatch.LocalBoundaryIsometry
public import Proof.CalderonPatch.InteriorCompletion

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X metricPair)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace (EuclideanHalfSpace n) M₁]
  [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace (EuclideanHalfSpace n) M₂]
  [IsManifold (𝓡∂ n) ∞ M₁] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "H" => inwardHalfSpace n
local notation "P" => positiveHalfSpace n

variable {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
  {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e)
  (hs : e.source = (𝓡∂ n).interior M₂) (ht : e.target = (𝓡∂ n).interior M₁)
  {f : M₂ ≃ₜ M₁} (hf : EqOn f e e.source)

theorem interiorIsometry_homeomorph_image
    (hs : e.source = (𝓡∂ n).interior M₂) (ht : e.target = (𝓡∂ n).interior M₁)
    (hf : EqOn f e e.source) :
    (f : M₂ → M₁) '' (𝓡∂ n).interior M₂ = (𝓡∂ n).interior M₁ := by
  rw [← hs, ← ht]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x,hx,rfl⟩
    rw [hf hx]
    exact e.map_source hx
  · intro y hy
    refine ⟨e.symm y,e.map_target hy,?_⟩
    rw [hf (e.map_target hy), e.right_inv hy]

variable {p : M₂} {p₁ : M₁} (D₂ : NativeBoundaryMetricChart g₂ p) (D₁ : NativeBoundaryMetricChart g₁ p₁)

private theorem coordTransition_map_into_chart
    (hs : e.source = (𝓡∂ n).interior M₂) (ht : e.target = (𝓡∂ n).interior M₁)
    (hf : EqOn f e e.source)
    {U : Set (X n)} (hU : U ⊆ D₂.ambient)
    (hTarget : MapsTo (f ∘ D₂.coord.symm) (U ∩ H) D₁.coord.source) :
    MapsTo (D₁.coord ∘ f ∘ D₂.coord.symm) (U ∩ P) (D₁.ambient ∩ P) := by
  intro x hx
  have hx' : x ∈ U ∩ H := ⟨hx.1,positiveHalfSpace_subset_inwardHalfSpace hx.2⟩
  have hxT : x ∈ D₂.coord.target := D₂.target_eq.symm ▸ ⟨hU hx.1,hx'.2⟩
  have hyS : f (D₂.coord.symm x) ∈ D₁.coord.source := hTarget hx'
  have hyI : f (D₂.coord.symm x) ∈ (𝓡∂ n).interior M₁ := by
    rw [← interiorIsometry_homeomorph_image hs ht hf]
    apply mem_image_of_mem
    apply (D₂.interior_iff _ (D₂.coord.map_target hxT)).mpr
    rw [D₂.coord.right_inv hxT]
    exact hx.2
  exact ⟨(D₁.target_eq ▸ D₁.coord.map_source hyS : _ ∈ D₁.ambient ∩ H).1,
    (D₁.interior_iff _ hyS).mp hyI⟩

private theorem coordTransition_metric
    (he : IsLocalMetricIsometry g₁ g₂ e)
    (hs : e.source = (𝓡∂ n).interior M₂) (hf : EqOn f e e.source)
    {U : Set (X n)} (hU : IsOpen U) (hUD : U ⊆ D₂.ambient)
    (hTarget : MapsTo (f ∘ D₂.coord.symm) (U ∩ H) D₁.coord.source)
    {x : X n} (hx : x ∈ U ∩ P) (v w : X n) :
    let a := D₁.coord ∘ f ∘ D₂.coord.symm
    metricPair D₂.field x v w =
      metricPair D₁.field (a x) (fderiv ℝ a x v) (fderiv ℝ a x w) := by
  let y := D₂.coord.symm x
  let z := f y
  let a : X n → X n := D₁.coord ∘ f ∘ D₂.coord.symm
  let W := U ∩ P
  have hW : IsOpen W := hU.inter isOpen_positiveHalfSpace
  have hWT : W ⊆ D₂.coord.target := fun _ hx =>
    D₂.target_eq.symm ▸ ⟨hUD hx.1, positiveHalfSpace_subset_inwardHalfSpace hx.2⟩
  have hyS : y ∈ D₂.coord.source := D₂.coord.map_target (hWT hx)
  have hyE : y ∈ e.source := by
    rw [hs, D₂.interior_iff _ hyS, D₂.coord.right_inv (hWT hx)]
    exact hx.2
  have hzS : z ∈ D₁.coord.source := hTarget ⟨hx.1,positiveHalfSpace_subset_inwardHalfSpace hx.2⟩
  have hA₂ := (D₂.smooth.contMDiffAt (D₂.open_source.mem_nhds hyS)).mdifferentiableAt (by simp)
  have hB₂ := ((D₂.smooth_inverse.mono hWT).contMDiffAt (hW.mem_nhds hx)).mdifferentiableAt (by simp)
  have hA₁ := (D₁.smooth.contMDiffAt (D₁.open_source.mem_nhds hzS)).mdifferentiableAt (by simp)
  have heq : (f : M₂ → M₁) =ᶠ[𝓝 y] e := Filter.mem_of_superset
    (e.open_source.mem_nhds hyE) hf
  have hF := ((he.smooth.contMDiffAt (e.open_source.mem_nhds hyE)).mdifferentiableAt (by simp)).congr_of_eventuallyEq heq
  let A₂ : TangentSpace J y →L[ℝ] X n := mfderiv J K D₂.coord y
  let B₂ : X n →L[ℝ] TangentSpace J y := mfderiv K J D₂.coord.symm x
  let A₁ : TangentSpace J z →L[ℝ] X n := mfderiv J K D₁.coord z
  let E : TangentSpace J y →L[ℝ] TangentSpace J z := mfderiv J J f y
  have hAB : A₂.comp B₂ = ContinuousLinearMap.id ℝ (X n) := by
    have hh := mfderiv_comp x hA₂ hB₂
    have heq : (D₂.coord : M₂ → X n) ∘ D₂.coord.symm =ᶠ[𝓝 x] id :=
      Filter.mem_of_superset (hW.mem_nhds hx) (fun _ hp => D₂.coord.right_inv (hWT hp))
    change mfderiv K K ((D₂.coord : M₂ → X n) ∘ D₂.coord.symm) x = A₂.comp B₂ at hh
    have hi : mfderiv K K ((D₂.coord : M₂ → X n) ∘ D₂.coord.symm) x =
        ContinuousLinearMap.id ℝ (X n) := heq.mfderiv_eq.trans mfderiv_id
    exact hh.symm.trans hi
  have hDF : fderiv ℝ a x = A₁.comp (E.comp B₂) := by
    have hh := mfderiv_comp x hA₁ (hF.comp x hB₂)
    rw [mfderiv_comp x hF hB₂] at hh
    exact (mfderiv_eq_fderiv (f := a) (x := x)).symm.trans hh
  have hIs (u t : TangentSpace J y) : g₂.inner y u t = g₁.inner z (E u) (E t) := by
    have hZ : z = e y := hf hyE
    have hE : E = mfderiv J J e y := heq.mfderiv_eq
    exact (he.metric_eq y hyE u t).trans (by
      rw [hE]
      exact congrArg (fun q => g₁.inner q ((mfderiv J J e y) u : X n) ((mfderiv J J e y) t : X n)) hZ.symm)
  have hBase := D₂.coord.right_inv (hWT hx)
  have h₂ := D₂.realizes y hyS (B₂ v) (B₂ w)
  change _ = metricPair D₂.field (D₂.coord y) (A₂ (B₂ v)) (A₂ (B₂ w)) at h₂
  rw [show D₂.coord y = x from hBase,
    show A₂ (B₂ v) = v from DFunLike.congr_fun hAB v,
    show A₂ (B₂ w) = w from DFunLike.congr_fun hAB w] at h₂
  have h₁ := D₁.realizes z hzS (E (B₂ v)) (E (B₂ w))
  change _ = metricPair D₁.field (a x) (A₁ (E (B₂ v))) (A₁ (E (B₂ w))) at h₁
  exact h₂.symm.trans ((hIs _ _).trans (h₁.trans (by rw [hDF]; rfl)))

include he hs ht hf in
/-- In normal boundary charts an interior isometry that extends
homeomorphically is a one-sided continuous coordinate map and is an
isometry on the positive side. -/
theorem exists_boundaryCoordinateIsometry (hBase : f p = p₁) :
    let a : X n → X n := D₁.coord ∘ f ∘ D₂.coord.symm
    ∃ U : Set (X n), IsOpen U ∧ D₂.coord p ∈ U ∧ U ⊆ D₂.ambient ∧
      MapsTo (f ∘ D₂.coord.symm) (U ∩ H) D₁.coord.source ∧
      ContinuousOn a (U ∩ H) ∧ ContDiffOn ℝ ∞ a (U ∩ P) ∧
      MapsTo a (U ∩ P) D₁.ambient ∧
      (∀ x ∈ U ∩ {x | x (0 : I n) = 0}, a x 0 = 0) ∧
      ∀ x ∈ U ∩ P, ∀ v w, metricPair D₂.field x v w =
        metricPair D₁.field (a x) (fderiv ℝ a x v) (fderiv ℝ a x w) := by
  let q := D₂.coord p
  let a : X n → X n := D₁.coord ∘ f ∘ D₂.coord.symm
  have hqT : q ∈ D₂.coord.target := D₂.coord.map_source D₂.point_source
  have hqAmb : q ∈ D₂.ambient := (D₂.target_eq ▸ hqT : q ∈ D₂.ambient ∩ H).1
  have hqL : D₂.coord.symm q = p := D₂.coord.left_inv D₂.point_source
  have hC : ContinuousOn (f ∘ D₂.coord.symm) D₂.coord.target :=
    f.continuous.comp_continuousOn D₂.smooth_inverse.continuousOn
  have hHere : (f ∘ D₂.coord.symm) q ∈ D₁.coord.source := by
    rw [Function.comp_apply, hqL, hBase]
    exact D₁.point_source
  have hGood : ∀ᶠ x in 𝓝[D₂.coord.target] q, (f ∘ D₂.coord.symm) x ∈ D₁.coord.source :=
    (hC q hqT).eventually_mem (D₁.open_source.mem_nhds hHere)
  have hAnear : ∀ᶠ x in 𝓝 q, x ∈ D₂.ambient := D₂.open_ambient.mem_nhds hqAmb
  have hNear := hAnear.and (eventually_nhdsWithin_iff.mp hGood)
  obtain ⟨U,hLoc,hU,hqU⟩ := _root_.eventually_nhds_iff.mp hNear
  have hUD : U ⊆ D₂.ambient := fun _ hx => (hLoc _ hx).1
  have hUH : U ∩ H ⊆ D₂.coord.target := fun x hx => D₂.target_eq.symm ▸ ⟨hUD hx.1,hx.2⟩
  have hTarget : MapsTo (f ∘ D₂.coord.symm) (U ∩ H) D₁.coord.source :=
    fun x hx => (hLoc x hx.1).2 (hUH hx)
  have hPosU : U ∩ P ⊆ U ∩ H := fun _ hx => ⟨hx.1,positiveHalfSpace_subset_inwardHalfSpace hx.2⟩
  have hUI : MapsTo D₂.coord.symm (U ∩ P) ((𝓡∂ n).interior M₂) := by
    intro x hx
    have hx' := hUH (hPosU hx)
    apply (D₂.interior_iff _ (D₂.coord.map_target hx')).mpr
    rw [D₂.coord.right_inv hx']
    exact hx.2
  have hF : ContMDiffOn J J ∞ f ((𝓡∂ n).interior M₂) :=
    hs ▸ he.smooth.congr hf
  have ha : ContDiffOn ℝ ∞ a (U ∩ P) :=
    (D₁.smooth.comp (hF.comp (D₂.smooth_inverse.mono (hPosU.trans hUH)) hUI)
      (hTarget.mono_left hPosU)).contDiffOn
  have hc : ContinuousOn a (U ∩ H) :=
    D₁.smooth.continuousOn.comp (hC.mono hUH) hTarget
  refine ⟨U,hU,hqU,hUD,hTarget,hc,ha,
    fun _ hx => (coordTransition_map_into_chart D₂ D₁ hs ht hf hUD hTarget hx).1,?_,?_⟩
  · intro x hx
    have hxH : x ∈ U ∩ H := ⟨hx.1,(mem_inwardHalfSpace).mpr (by
      have h : x 0 = 0 := hx.2
      rw [h])⟩
    have hxT := hUH hxH
    have hyS : f (D₂.coord.symm x) ∈ D₁.coord.source := hTarget hxH
    have hPos : ¬ a x ∈ P := by
      intro ha
      have hI := (D₁.interior_iff _ hyS).mpr ha
      rw [← interiorIsometry_homeomorph_image hs ht hf] at hI
      obtain ⟨y,hy,hxy⟩ := hI
      have hEq : y = D₂.coord.symm x := f.injective hxy
      have hxi := (D₂.interior_iff _ (D₂.coord.map_target hxT)).mp (hEq ▸ hy)
      rw [D₂.coord.right_inv hxT] at hxi
      exact ((mem_positiveHalfSpace).mp hxi).ne' hx.2
    have hNonneg : 0 ≤ a x 0 :=
      (mem_inwardHalfSpace).mp ((D₁.target_eq ▸ D₁.coord.map_source hyS) : a x ∈ D₁.ambient ∩ H).2
    exact le_antisymm (le_of_not_gt (fun hp => hPos ((mem_positiveHalfSpace).mpr hp))) hNonneg
  · exact fun _ hx v w => coordTransition_metric D₂ D₁ he hs hf hU hUD hTarget hx v w

end CalderonPatch
