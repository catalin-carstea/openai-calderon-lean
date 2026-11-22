module

public import Proof.CalderonPatch.MatchedCapMetrics
public import Proof.CalderonPatch.CapSeam
public import Proof.CalderonPatch.CapTraceSupport
public import Proof.CalderonPatch.CauchyNormalJets
public import Proof.CalderonPatch.CommonBoundaryCoordinates
public import Proof.CalderonPatch.SignedCapBox

import Mathlib.Tactic.Linarith

public section

noncomputable section
open Metric Set Filter
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField chartDerivativeWord metricPair)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "Zt" => boundaryTangentPlane (0 : I n)
local notation "H" => inwardHalfSpace n

/-- One side of the cap, with its unpushed signed metric and its
relationship to the original embedding. -/
structure AttachedCapSide (A : ProductBoundaryChart (n := n) (M := M) (Z := Zt))
    (γ : MetricField n) (G : SmoothMetric n M) (cap : Set M) (embed : M → M)
    (height : Zt → ℝ) (push : (Zt × ℝ) ≃ (Zt × ℝ)) where
  shift : CapShift A
  cap_eq : cap = shift.cap
  embed_eq : embed = shift.embed
  height_eq : shift.capHeight = height
  push_eq : shift.coordinateShift = push
  field : MetricField n
  smooth_field : CalderonN.SmoothMetric ((inwardChartSplit (n := n)) ⁻¹' A.ambient) field
  inward_field : EqOn field γ H
  realizes : ∀ x ∈ A.coord.source,
    G.inner x = nativeCoordinateBilinear field
      ((inwardChartSplit (n := n)).symm ∘ push.symm ∘ A.coord) x

/-- The shared box and vertical push, together with both native
signed readings and their identifications on the cap and the seam. -/
structure CommonCapCoordinates {W : Set (Zt × ℝ)} {z₀ : Zt}
    (A₁ A₂ : ProductBoundaryChart (n := n) (M := M) (Z := Zt))
    (γ₁ γ₂ : MetricField n) (G₁ G₂ : SmoothMetric n M)
    (capMap : OpenPartialHomeomorph M M) (embed₁ embed₂ : M → M) where
  box : SignedCapBox W z₀
  height : Zt → ℝ
  smooth_height : ContDiff ℝ ∞ height
  height_bound : ∀ z, 0 ≤ height z ∧ height z < box.radius
  height_support : {z | 0 < height z} = ball z₀ box.radius
  push : (Zt × ℝ) ≃ (Zt × ℝ)
  smooth_push : ContDiff ℝ ∞ push
  smooth_push_inverse : ContDiff ℝ ∞ push.symm
  push_tangential : ∀ q, (push q).1 = q.1
  push_seam : ∀ z, push (z,0) = (z,height z)
  push_boundary : ∀ z, push (z,-height z) = (z,0)
  push_monotone : ∀ z, StrictMono (fun t => (push (z,t)).2)
  first : AttachedCapSide A₁ γ₁ G₁ capMap.target embed₁ height push
  second : AttachedCapSide A₂ γ₂ G₂ capMap.source embed₂ height push
  charts_map : (capMap : M → M) = A₁.coord.symm ∘ A₂.coord
  fields_eq : EqOn first.field second.field Hᶜ
  original_fields_eq : EqOn γ₁ γ₂
    (((inwardChartSplit (n := n)) ⁻¹' W) ∩ {x | x (0 : I n) = 0})

/-- Matched normal metric jets in the common signed coordinates give actual
smooth Riemannian cap extensions with an isometry on the open caps.
A continuation of that isometry agrees at the covered original seam. -/
theorem exists_attached_commonCap_of_matched_jets
    (g₁ g₂ : SmoothMetric n M)
    (D₁ D₂ : ProductBoundaryChart (n := n) (M := M) (Z := Zt))
    {W : Set (Zt × ℝ)} (hW : IsOpen W) (hWD₁ : W ⊆ D₁.ambient) (hWD₂ : W ⊆ D₂.ambient)
    (z₀ : Zt) (hZ : (z₀,(0 : ℝ)) ∈ W)
    {Γ : Set ((J).boundary M)} (p₀ : (J).boundary M)
    (hp₀ : (p₀ : M) ∈ D₂.coord.source) (hp₀c : D₂.coord p₀ = (z₀, 0))
    (hTrace₁ : ∀ p : (J).boundary M, (p : M) ∈ D₁.coord.source → D₁.coord p ∈ W → p ∈ Γ)
    (hCommon : ∀ p : (J).boundary M, (p : M) ∈ D₂.coord.source → D₂.coord p ∈ W →
      (p : M) ∈ D₁.coord.source ∧ D₁.coord p = D₂.coord p ∧ p ∈ Γ)
    {γ₁ γ₂ : MetricField n}
    (hγ₁ : CalderonN.SmoothMetric (inwardChartSplit ⁻¹' W) γ₁)
    (hγ₂ : CalderonN.SmoothMetric (inwardChartSplit ⁻¹' W) γ₂)
    (hNative₁ : ∀ x ∈ D₁.coord.source,
      nativeCoordinateBilinear γ₁ (inwardChartSplit.symm ∘ D₁.coord) x = g₁.inner x)
    (hNative₂ : ∀ x ∈ D₂.coord.source,
      nativeCoordinateBilinear γ₂ (inwardChartSplit.symm ∘ D₂.coord) x = g₂.inner x)
    (hJets : ∀ (i j : I n) (k : ℕ), EqOn
      (chartDerivativeWord (List.replicate k 0) (fun x => γ₁ x i j))
      (chartDerivativeWord (List.replicate k 0) (fun x => γ₂ x i j))
      ((inwardChartSplit ⁻¹' W) ∩ {x | x (0 : I n) = 0})) :
    ∃ (G₁ G₂ : SmoothMetric n M) (eCap : OpenPartialHomeomorph M M),
      IsConnected eCap.source ∧ IsConnected eCap.target ∧
      eCap.source ⊆ (J).interior M ∧ eCap.target ⊆ (J).interior M ∧
      IsLocalMetricIsometry G₁ G₂ eCap ∧
      ∃ (O₁ : OriginalCopy g₁ G₁ eCap.target) (O₂ : OriginalCopy g₂ G₂ eCap.source)
        (patch : Set ((J).boundary M)), IsOpen patch ∧ patch.Nonempty ∧ patch ⊆ Γ ∧
          (∀ w : M → ℝ, EqOn w 0 ((J).boundary M) →
            tsupport (fun p : (J).boundary M => w (O₁.embed p)) ⊆ Γ ∧
            tsupport (fun p : (J).boundary M => w (O₂.embed p)) ⊆ Γ) ∧
          (∀ e : OpenPartialHomeomorph M M, e.source = (J).interior M → EqOn e eCap eCap.source →
            ∀ p ∈ patch, O₂.embed p ∈ e.source ∧ e (O₂.embed p) = O₁.embed p) ∧
          Nonempty (CommonCapCoordinates (W := W) (z₀ := z₀)
            (D₁.restrictAmbient hW hWD₁) (D₂.restrictAmbient hW hWD₂) γ₁ γ₂
            G₁ G₂ eCap O₁.embed O₂.embed) := by
  let A₁ := D₁.restrictAmbient hW hWD₁
  let A₂ := D₂.restrictAmbient hW hWD₂
  let L := inwardChartSplit (n := n)
  obtain ⟨B⟩ := exists_signedCapBox hW hZ
  let r := B.radius
  have hr : 0 < r := B.radius_pos
  have hFit : closedBall z₀ r ×ˢ Icc (-r) r ⊆ W := B.support_inside
  obtain ⟨b,e,hb,hbnd,hbpos,he,hei,heId,heSeam,heH,heI,heT,heGraph,heM⟩ :=
    exists_small_vertical_cap_with_graph z₀ hr hr
  let C₁ := capShift_of_vertical A₁ z₀ hr hFit b e hb hbnd hbpos he hei heId heH heI
  let C₂ := capShift_of_vertical A₂ z₀ hr hFit b e hb hbnd hbpos he hei heId heH heI
  let E := pushedCap b
  have hC₁ : C₁.cap = A₁.coord.symm '' E := C₁.cap_eq
  have hC₂ : C₂.cap = A₂.coord.symm '' E := C₂.cap_eq
  have hE : E ⊆ W ∩ (univ ×ˢ Ici (0 : ℝ)) := by
    intro x hx
    have hh : 0 < x.2 ∧ x.2 < b x.1 := hx
    have hz : x.1 ∈ ball z₀ r := hbpos ▸ hh.1.trans hh.2
    have ht : x.2 < r := hh.2.trans (hbnd _).2
    exact ⟨hFit ⟨ball_subset_closedBall hz,⟨by linarith [hh.1],ht.le⟩⟩,mem_univ _,hh.1.le⟩
  have hE₁ : E ⊆ A₁.coord.target := A₁.target_eq.symm ▸ hE
  have hE₂ : E ⊆ A₂.coord.target := A₂.target_eq.symm ▸ hE
  have hSC₁ : C₁.cap ⊆ A₁.coord.source := by
    rw [hC₁]
    rintro _ ⟨x,hx,rfl⟩
    exact A₁.coord.map_target (hE₁ hx)
  have hSC₂ : C₂.cap ⊆ A₂.coord.source := by
    rw [hC₂]
    rintro _ ⟨x,hx,rfl⟩
    exact A₂.coord.map_target (hE₂ hx)
  have hc₁ : MapsTo A₁.coord C₁.cap E := by
    rw [hC₁]
    rintro _ ⟨x,hx,rfl⟩
    rwa [A₁.coord.right_inv (hE₁ hx)]
  have hc₂ : MapsTo A₂.coord C₂.cap E := by
    rw [hC₂]
    rintro _ ⟨x,hx,rfl⟩
    rwa [A₂.coord.right_inv (hE₂ hx)]
  have hTo₁ : MapsTo (A₁.coord.symm ∘ A₂.coord) C₂.cap C₁.cap := by
    intro x hx
    rw [hC₁]
    exact mem_image_of_mem _ (hc₂ hx)
  have hTo₂ : MapsTo (A₂.coord.symm ∘ A₁.coord) C₁.cap C₂.cap := by
    intro x hx
    rw [hC₂]
    exact mem_image_of_mem _ (hc₁ hx)
  have hF := (A₁.smooth_inverse.mono hE₁).comp (A₂.smooth.mono hSC₂) hc₂
  have hFi := (A₂.smooth_inverse.mono hE₂).comp (A₁.smooth.mono hSC₁) hc₁
  let eCap : OpenPartialHomeomorph M M :=
    { toFun := A₁.coord.symm ∘ A₂.coord
      invFun := A₂.coord.symm ∘ A₁.coord
      source := C₂.cap
      target := C₁.cap
      map_source' := hTo₁
      map_target' := hTo₂
      left_inv' := fun x hx => by
        simp only [Function.comp_apply, A₁.coord.right_inv (hE₁ (hc₂ hx)), A₂.coord.left_inv (hSC₂ hx)]
      right_inv' := fun x hx => by
        simp only [Function.comp_apply, A₂.coord.right_inv (hE₂ (hc₁ hx)), A₁.coord.left_inv (hSC₁ hx)]
      continuousOn_toFun := hF.continuousOn
      continuousOn_invFun := hFi.continuousOn
      open_source := C₂.open_cap
      open_target := C₁.open_cap }
  have hFull (i j : I n) := iteratedFDeriv_eqOn_of_pure_normal_jets_local
    (hW.preimage L.continuous) (hγ₁.1 i j) (hγ₂.1 i j) (hJets i j)
  obtain ⟨γe₁,γe₂,hg₁,hg₂,hγe₁,hγe₂,hγeq⟩ :=
    exists_matched_signed_metric_extensions (hW.preimage L.continuous) hγ₁ hγ₂ hFull
  have hNativeA₁ (x : M) (hx : x ∈ A₁.coord.source) :
      nativeCoordinateBilinear γ₁ (L.symm ∘ A₁.coord) x = g₁.inner x := hNative₁ x hx.1
  have hNativeA₂ (x : M) (hx : x ∈ A₂.coord.source) :
      nativeCoordinateBilinear γ₂ (L.symm ∘ A₂.coord) x = g₂.inner x := hNative₂ x hx.1
  obtain ⟨G₁,O₁,hO₁,hG₁⟩ := exists_originalCopy_of_capShift g₁ A₁ C₁ hg₁
    (hγe₁.mono inter_subset_right) hNativeA₁
  obtain ⟨G₂,O₂,hO₂,hG₂⟩ := exists_originalCopy_of_capShift g₂ A₂ C₂ hg₂
    (hγe₂.mono inter_subset_right) hNativeA₂
  let patch : Set ((J).boundary M) := {p | (p : M) ∈ A₂.coord.source ∧ 0 < b (A₂.coord p).1}
  have hOpenP : IsOpen patch := by
    let V := {x : Zt × ℝ | 0 < b x.1}
    have hV : IsOpen V := isOpen_lt continuous_const (hb.continuous.comp continuous_fst)
    exact (A₂.smooth.continuousOn.isOpen_inter_preimage A₂.open_source hV).preimage continuous_subtype_val
  have hp₀a : (p₀ : M) ∈ A₂.coord.source := by
    refine ⟨hp₀, ?_⟩
    change D₂.coord p₀ ∈ W
    rwa [hp₀c]
  have hPair (p : (J).boundary M) (hp : p ∈ patch) :
      (p : M) ∈ A₁.coord.source ∧ A₁.coord p = A₂.coord p ∧ p ∈ Γ := by
    have hpS : (p : M) ∈ D₂.coord.source ∩ D₂.coord ⁻¹' W := hp.1
    obtain ⟨h₁,hEq,hΓ⟩ := hCommon p hpS.1 hpS.2
    refine ⟨⟨h₁,?_⟩,hEq,hΓ⟩
    change D₁.coord p ∈ W
    rw [hEq]
    exact hpS.2
  have hneP : patch.Nonempty := by
    refine ⟨p₀, hp₀a, ?_⟩
    change 0 < b (D₂.coord p₀).1
    rw [hp₀c]
    change z₀ ∈ {z | 0 < b z}
    rw [hbpos]
    exact mem_ball_self hr
  have hData : Nonempty (CommonCapCoordinates (W := W) (z₀ := z₀) A₁ A₂ γ₁ γ₂
      G₁ G₂ eCap O₁.embed O₂.embed) :=
    ⟨{ box := B
       height := b
       smooth_height := hb
       height_bound := hbnd
       height_support := hbpos
       push := e
       smooth_push := he
       smooth_push_inverse := hei
       push_tangential := heT
       push_seam := heSeam
       push_boundary := heGraph
       push_monotone := heM
       first := ⟨C₁,rfl,hO₁,rfl,rfl,γe₁,hg₁,hγe₁,hG₁⟩
       second := ⟨C₂,rfl,hO₂,rfl,rfl,γe₂,hg₂,hγe₂,hG₂⟩
       charts_map := rfl
       fields_eq := hγeq
       original_fields_eq := fun x hx => by
         ext i j
         simpa [chartDerivativeWord] using hJets i j 0 hx }⟩
  refine ⟨G₁,G₂,eCap,C₂.connected_cap,C₁.connected_cap,C₂.cap_interior,C₁.cap_interior,
    ⟨hF,hFi,?_⟩,O₁,O₂,patch,hOpenP,hneP,(fun p hp => (hPair p hp).2.2),?_,?_,hData⟩
  rotate_left
  · intro w hw
    rw [hO₁,hO₂]
    constructor
    · apply C₁.trace_support_subset _ hw
      intro p hp
      have h := C₁.support_in_chart hp
      exact hTrace₁ p h.1 h.2
    · apply C₂.trace_support_subset _ hw
      intro p hp
      have h := C₂.support_in_chart hp
      exact (hCommon p h.1 h.2).2.2
  · intro f hf hEq p hp
    obtain ⟨hp₁,hq,_⟩ := hPair p hp
    have hp₂ : (p : M) ∈ A₂.coord.source := hp.1
    have hpos : 0 < b (A₂.coord p).1 := hp.2
    have ht := A₂.height_eq_zero_on_boundary p.property hp₂
    have hc₂ : A₂.coord p = ((A₂.coord p).1,0) := Prod.ext rfl ht
    have hc₁' := hq.trans hc₂
    have hEeq : EqOn (f ∘ A₂.coord.symm) A₁.coord.symm E := by
      intro x hx
      have hCapx : A₂.coord.symm x ∈ eCap.source := by
        change A₂.coord.symm x ∈ C₂.cap
        rw [hC₂]
        exact mem_image_of_mem _ hx
      change f (A₂.coord.symm x) = _
      rw [hEq hCapx]
      change A₁.coord.symm (A₂.coord (A₂.coord.symm x)) = _
      rw [A₂.coord.right_inv (hE₂ hx)]
    rw [hO₁,hO₂]
    exact eq_on_capSeam_of_eq_on_pushedCap C₁ C₂ hpos (heSeam _) (heSeam _)
      hE₁ hE₂ hp₁ hp₂ hc₁' hc₂ f hf hEeq
  let Q₁ : M → X n := L.symm ∘ e.symm ∘ A₁.coord
  let Q₂ : M → X n := L.symm ∘ e.symm ∘ A₂.coord
  intro x hx v w
  have hx' : x ∈ C₂.cap := hx
  let y := eCap x
  have hy : y ∈ C₁.cap := hTo₁ hx'
  have hQ₁ : ContMDiffOn J K ∞ Q₁ A₁.coord.source :=
    L.symm.contDiff.contMDiff.comp_contMDiffOn (hei.contMDiff.comp_contMDiffOn A₁.smooth)
  have hQnear : Q₁ ∘ eCap =ᶠ[𝓝 x] Q₂ := by
    filter_upwards [C₂.open_cap.mem_nhds hx'] with p hp
    change L.symm (e.symm (A₁.coord (A₁.coord.symm (A₂.coord p)))) = _
    rw [A₁.coord.right_inv (hE₁ (hc₂ hp))]
    rfl
  have heq := mfderiv_comp x
    ((hQ₁.contMDiffAt (A₁.open_source.mem_nhds (hSC₁ hy))).mdifferentiableAt (by simp))
    ((hF.contMDiffAt (C₂.open_cap.mem_nhds hx')).mdifferentiableAt (by simp))
  change mfderiv J K (Q₁ ∘ eCap) x =
    (mfderiv J K Q₁ y).comp (mfderiv J J eCap x) at heq
  have hD : (mfderiv J K Q₂ x : TangentSpace J x →L[ℝ] X n) =
    (mfderiv J K Q₁ y).comp (mfderiv J J eCap x) := hQnear.mfderiv_eq.symm.trans heq
  have hQx : Q₁ y = Q₂ x := hQnear.eq_of_nhds
  have hExterior : Q₂ x ∈ Hᶜ := by
    intro hn
    let ξ := A₂.coord x
    have hη : e.symm ξ ∈ univ ×ˢ Ici (0 : ℝ) :=
      ⟨mem_univ _,by
        have hL := inwardChartSplit_height (L.symm (e.symm ξ))
        change (L (L.symm (e.symm ξ))).2 = _ at hL
        rw [L.apply_symm_apply] at hL
        rw [hL]
        exact (mem_inwardHalfSpace).mp hn⟩
    have heP := mem_image_of_mem e hη
    rw [e.apply_symm_apply, heH] at heP
    have hCap : ξ ∈ E := hc₂ hx'
    exact (not_le_of_gt (show 0 < ξ.2 ∧ ξ.2 < b ξ.1 from hCap).2) heP
  have hv := DFunLike.congr_fun hD v
  have hw := DFunLike.congr_fun hD w
  change G₂.inner x v w = G₁.inner y (mfderiv J J eCap x v) (mfderiv J J eCap x w)
  have hG₁' : G₁.inner y = nativeCoordinateBilinear γe₁ Q₁ y := hG₁ y (hSC₁ hy)
  have hG₂' : G₂.inner x = nativeCoordinateBilinear γe₂ Q₂ x := hG₂ x (hSC₂ hx')
  rw [hG₂',hG₁',nativeCoordinateBilinear_apply,nativeCoordinateBilinear_apply]
  let B : TangentSpace J x →L[ℝ] X n := mfderiv J K Q₂ x
  let A : TangentSpace J x →L[ℝ] X n := (mfderiv J K Q₁ y).comp (mfderiv J J eCap x)
  have hBA : B = A := hD
  change metricPair γe₂ (Q₂ x) (B v) (B w) = metricPair γe₁ (Q₁ y) (A v) (A w)
  rw [hBA,hQx]
  simp only [metricPair, hγeq hExterior]

end CalderonPatch
