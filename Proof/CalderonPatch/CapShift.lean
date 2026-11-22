module

public import Proof.CalderonPatch.SmallVerticalCap
public import Proof.CalderonPatch.ConnectedInterior

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

theorem equiv_mem_of_fixes_outside {E : Type*} {e : E ≃ E} {U : Set E}
    (h : EqOn e id Uᶜ) (x : E) : e x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    by_contra hx'
    have he : e x = x := h hx'
    rw [he] at hx
    exact hx' hx
  · intro hx
    by_contra hx'
    have he : e (e x) = e x := h hx'
    exact hx' ((e.injective he).symm ▸ hx)

/-- A fixed compactly supported vertical shift can be used in
different boundary charts so their added caps carry common coordinates. -/
@[expose] def capShift_of_vertical (D : ProductBoundaryChart (n := n) (M := M) (Z := Z))
    (z₀ : Z) {a r : ℝ} (ha : 0 < a)
    (hFit : closedBall z₀ a ×ˢ Icc (-r) r ⊆ D.ambient)
    (b : Z → ℝ) (e : (Z × ℝ) ≃ (Z × ℝ))
    (hb : ContDiff ℝ ∞ b) (hbnd : ∀ z, 0 ≤ b z ∧ b z < r)
    (hbpos : {z | 0 < b z} = ball z₀ a)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    (heId : EqOn e id (ball z₀ a ×ˢ Ioo (-r) r)ᶜ)
    (heH : e '' (univ ×ˢ Ici (0 : ℝ)) = {p | b p.1 ≤ p.2})
    (heI : e '' (univ ×ˢ Ioi (0 : ℝ)) = {p | b p.1 < p.2}) :
    CapShift D := by
  classical
  let c := D.coord
  let W := D.ambient
  let H : Set (Z × ℝ) := univ ×ˢ Ici 0
  let P : Set (Z × ℝ) := univ ×ˢ Ioi 0
  let L := closedBall z₀ a ×ˢ Icc (-r) r
  let A := c.symm '' (L ∩ H)
  let E := pushedCap b
  let cap := c.symm '' E
  have hT : c.target = W ∩ H := D.target_eq
  have hLH : L ∩ H ⊆ c.target := hT.symm ▸ inter_subset_inter_left H hFit
  have hLc : IsCompact (L ∩ H) := ((isCompact_closedBall _ _).prod isCompact_Icc).inter_right
    (isClosed_univ.prod isClosed_Ici)
  have hA : IsClosed A := (hLc.image_of_continuousOn (D.smooth_inverse.continuousOn.mono hLH)).isClosed
  have hAs : A ⊆ c.source := by
    rintro _ ⟨p,hp,rfl⟩
    exact c.map_target (hLH hp)
  have hFix : EqOn e id Lᶜ := by
    apply heId.mono
    exact compl_subset_compl.mpr (Set.prod_mono ball_subset_closedBall Ioo_subset_Icc_self)
  have heW (p : Z × ℝ) : e p ∈ W ↔ p ∈ W :=
    equiv_mem_of_fixes_outside (hFix.mono (compl_subset_compl.mpr hFit)) p
  have heiW (p : Z × ℝ) : e.symm p ∈ W ↔ p ∈ W := by rw [← heW (e.symm p), e.apply_symm_apply]
  have hTo : MapsTo e c.target c.target := by
    intro p hp
    have h := mem_image_of_mem e ((hT ▸ hp : p ∈ W ∩ H).2)
    change e p ∈ e '' (univ ×ˢ Ici 0) at h
    rw [heH] at h
    exact hT.symm ▸ ⟨(heW p).mpr (hT ▸ hp : p ∈ W ∩ H).1,
      mem_univ _, (hbnd (e p).1).1.trans (show b (e p).1 ≤ (e p).2 from h)⟩
  let f : M → M := c.source.piecewise (c.symm ∘ e ∘ c) id
  let g : M → M := c.source.piecewise (c.symm ∘ e.symm ∘ c) id
  have hfChart (x : M) (hx : x ∈ c.source) : f x = c.symm (e (c x)) :=
    piecewise_eq_of_mem _ _ _ hx
  have hgChart (x : M) (hx : x ∈ c.source) : g x = c.symm (e.symm (c x)) :=
    piecewise_eq_of_mem _ _ _ hx
  have hfOut (x : M) (hx : x ∉ A) : f x = x := by
    by_cases hxs : x ∈ c.source
    · have hxL : c x ∉ L := fun hp => hx ⟨c x, ⟨hp, (hT ▸ c.map_source hxs : c x ∈ W ∩ H).2⟩, c.left_inv hxs⟩
      rw [hfChart x hxs, hFix hxL, id_eq, c.left_inv hxs]
    · exact piecewise_eq_of_notMem _ _ _ hxs
  have hgOut (x : M) (hx : x ∉ A) : g x = x := by
    by_cases hxs : x ∈ c.source
    · have hxL : c x ∉ L := fun hp => hx ⟨c x, ⟨hp, (hT ▸ c.map_source hxs : c x ∈ W ∩ H).2⟩, c.left_inv hxs⟩
      have hInv : e.symm (c x) = c x := by
        apply e.injective
        rw [e.apply_symm_apply, hFix hxL, id_eq]
      rw [hgChart x hxs, hInv, c.left_inv hxs]
    · exact piecewise_eq_of_notMem _ _ _ hxs
  have hfMem (x : M) : f x ∈ c.source ↔ x ∈ c.source := by
    by_cases hx : x ∈ c.source
    · simp only [hx, iff_true, hfChart x hx]
      exact c.map_target (hTo (c.map_source hx))
    · rw [hfOut x (fun h => hx (hAs h))]
  have hfCoord (x : M) (hx : x ∈ c.source) : c (f x) = e (c x) := by
    rw [hfChart x hx, c.right_inv (hTo (c.map_source hx))]
  have hgLeft : Function.LeftInverse g f := by
    intro x
    by_cases hx : x ∈ c.source
    · rw [hgChart _ ((hfMem x).mpr hx), hfCoord x hx, e.symm_apply_apply, c.left_inv hx]
    · have h := fun h => hx (hAs h)
      rw [hfOut x h, hgOut x h]
  have hGmap : MapsTo (e.symm ∘ c) (range f ∩ c.source) c.target := by
    rintro _ ⟨⟨x,rfl⟩,hx⟩
    have hxs := (hfMem x).mp hx
    rw [Function.comp_apply, hfCoord x hxs, e.symm_apply_apply]
    exact c.map_source hxs
  have hF : ContMDiff J J ∞ f := by
    intro x
    by_cases hx : x ∈ c.source
    · apply ContMDiffAt.congr_of_eventuallyEq
        (((D.smooth_inverse.comp (he.contMDiff.comp_contMDiffOn D.smooth)
          (fun _ hx => hTo (c.map_source hx))).contMDiffAt (D.open_source.mem_nhds hx)))
      exact Filter.mem_of_superset (D.open_source.mem_nhds hx) (fun y hy => hfChart y hy)
    · have hn : x ∈ Aᶜ := fun h => hx (hAs h)
      apply ContMDiffAt.congr_of_eventuallyEq contMDiffAt_id
      exact Filter.mem_of_superset (hA.isOpen_compl.mem_nhds hn) (fun y hy => hfOut y hy)
  have hG : ContMDiffOn J J ∞ g (range f) := by
    intro x hx
    by_cases hxs : x ∈ c.source
    · have hlocal : ContMDiffOn J J ∞ (c.symm ∘ e.symm ∘ c) (range f ∩ c.source) :=
        D.smooth_inverse.comp ((hei.contMDiff.comp_contMDiffOn D.smooth).mono inter_subset_right) hGmap
      apply (contMDiffWithinAt_inter (D.open_source.mem_nhds hxs)).mp
      apply (hlocal x ⟨hx,hxs⟩).congr_of_eventuallyEq
      · exact Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => hgChart y hy.2)
      · exact hgChart x hxs
    · have hn : x ∈ Aᶜ := fun h => hxs (hAs h)
      exact contMDiffAt_id.contMDiffWithinAt.congr_of_eventuallyEq
        (Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds (hA.isOpen_compl.mem_nhds hn))
          (fun y hy => hgOut y hy)) (hgOut x hn)
  have hEL : E ⊆ L ∩ H := by
    intro p hp
    have hp' : 0 < p.2 ∧ p.2 < b p.1 := by simpa only [E, pushedCap, mem_ofPred_eq] using hp
    have hz : p.1 ∈ ball z₀ a := hbpos ▸ (hp'.1.trans hp'.2)
    have hrp : p.2 < r := hp'.2.trans (hbnd _).2
    exact ⟨⟨ball_subset_closedBall hz, ⟨by linarith [hp'.1], hrp.le⟩⟩, mem_univ _, hp'.1.le⟩
  have hET : E ⊆ c.target := hEL.trans hLH
  have hCap : cap = c.source ∩ c ⁻¹' E := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨c.map_target (hET hp), by change c (c.symm p) ∈ E; rwa [c.right_inv (hET hp)]⟩
    · rintro ⟨hx,hE⟩
      exact ⟨c x,hE,c.left_inv hx⟩
  have hCapo : IsOpen cap := hCap.symm ▸ D.smooth.continuousOn.isOpen_inter_preimage
    D.open_source (isOpen_pushedCap hb.continuous)
  have hEConn : IsConnected E := isConnected_pushedCap hb.continuous
    (hbpos.symm ▸ (convex_ball _ _).isConnected ⟨z₀, mem_ball_self ha⟩)
  have hCapI : cap ⊆ (J).interior M := by
    intro x hx
    rw [hCap] at hx
    have h : 0 < (c x).2 ∧ (c x).2 < b (c x).1 := by
      simpa only [E, pushedCap, mem_ofPred_eq] using (show c x ∈ E from hx.2)
    exact (D.interior_iff x hx.1).mpr h.1
  have hClo : closure cap ⊆ A := closure_minimal (image_mono hEL) hA
  have hCloCoord (x : M) (hx : x ∈ c.source) : x ∈ closure cap ↔ c x ∈ closure E := by
    constructor
    · intro h
      have hc : ContinuousAt c x := D.smooth.continuousOn.continuousAt (D.open_source.mem_nhds hx)
      have hSub : c '' cap ⊆ E := by
        rintro _ ⟨y, hy, rfl⟩
        exact (hCap ▸ hy : y ∈ c.source ∩ c ⁻¹' E).2
      exact closure_mono hSub (hc.continuousWithinAt.mem_closure_image h)
    · intro h
      have hc := (D.smooth_inverse.continuousOn (c x) (c.map_source hx)).mono hET
      have hh := hc.mem_closure_image h
      rwa [c.left_inv hx] at hh
  have hComp (x : M) (hx : x ∈ c.source) :
      x ∈ (J).interior M \ closure cap ↔ b (c x).1 < (c x).2 := by
    change (x ∈ (J).interior M ∧ x ∉ closure cap) ↔ _
    rw [D.interior_iff x hx, hCloCoord x hx]
    have hh := positiveHalfSpace_sdiff_closure_pushedCap hb.continuous (fun z => (hbnd z).1)
    simpa only [E, c, Set.mem_sdiff, mem_prod, mem_univ, true_and, mem_Ioi, mem_ofPred_eq] using
      (Set.ext_iff.mp hh (c x))
  have hImage : f '' (J).interior M = (J).interior M \ closure cap := by
    ext x
    by_cases hx : x ∈ c.source
    · rw [hComp x hx]
      constructor
      · rintro ⟨y,hy,rfl⟩
        have hys := (hfMem y).mp hx
        rw [hfCoord y hys]
        have hh := mem_image_of_mem e (show c y ∈ P from ⟨mem_univ _, (D.interior_iff y hys).mp hy⟩)
        rwa [heI] at hh
      · intro hx'
        have hh : c x ∈ e '' P := heI.symm ▸ hx'
        obtain ⟨p,hp,hpx⟩ := hh
        have hpW : p ∈ W := (heW p).mp (hpx.symm ▸ (hT ▸ c.map_source hx : c x ∈ W ∩ H).1)
        have hpT : p ∈ c.target := hT.symm ▸ ⟨hpW,mem_univ _,hp.2.le⟩
        refine ⟨c.symm p, (D.interior_iff _ (c.map_target hpT)).mpr ?_, ?_⟩
        · rw [c.right_inv hpT]
          exact hp.2
        · rw [hfChart _ (c.map_target hpT), c.right_inv hpT, hpx, c.left_inv hx]
    · have hNot : x ∉ closure cap := fun h => hx (hAs (hClo h))
      constructor
      · rintro ⟨y,hy,rfl⟩
        have hny : y ∉ c.source := fun h => hx ((hfMem y).mpr h)
        have heq := hfOut y (fun h => hny (hAs h))
        exact ⟨heq.symm ▸ hy,hNot⟩
      · intro hi
        exact ⟨x,hi.1,hfOut x (fun h => hx (hAs h))⟩
  exact ⟨f, g, cap, A, hA, hAs, fun x hx => hfOut x hx, hClo, hgLeft, hF, hG, hCapo, hEConn.image c.symm
    (D.smooth_inverse.continuousOn.mono hET), hCapI, hImage, e, he, hei,
    fun x hx => ⟨(hfMem x).mpr hx, hfCoord x hx⟩, heW, b, hb, rfl⟩

/-- A sufficiently small compact cylinder in the chart contains an
attached connected cap, a smooth original embedding, and an inverse
smooth on its image. -/
theorem exists_capShift (D : ProductBoundaryChart (n := n) (M := M) (Z := Z))
    (z₀ : Z) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hFit : closedBall z₀ a ×ˢ Icc (-r) r ⊆ D.ambient) :
    Nonempty (CapShift D) := by
  obtain ⟨b,e,hb,hbnd,hbpos,he,hei,heId,_,heH,heI⟩ := exists_small_vertical_cap z₀ ha hr
  exact ⟨capShift_of_vertical D z₀ ha hFit b e hb hbnd hbpos he hei heId heH heI⟩

end CalderonPatch
