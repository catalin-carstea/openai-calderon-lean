module

public import Proof.CalderonPatch.CapShift
public import Proof.CalderonPatch.BoundaryChartExtension
public import Proof.CalderonPatch.BoundaryNormalMetric

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Tactic

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField pullbackMetric)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "XH" => boundaryTangentPlane (0 : I n)

/-- The product chart uses inward rather than outward height. -/
def inwardChartSplit : X n ≃L[ℝ] XH × ℝ :=
  (boundaryChartSplit (0 : I n)).trans
    ((ContinuousLinearEquiv.refl ℝ XH).prodCongr (ContinuousLinearEquiv.neg ℝ))

theorem inwardChartSplit_height (x : X n) : (inwardChartSplit x).2 = x 0 := by
  change -(boundaryChartSplit (0 : I n) x).2 = x 0
  rw [boundaryChartSplit_height, neg_neg]

theorem inwardChartSplit_tangent (x : X n) :
    ((inwardChartSplit x).1 : X n) = boundaryFoot 0 x := by
  change ((boundaryChartSplit (0 : I n) x).1 : X n) = _
  exact boundaryChartSplit_tangent 0 x

/-- The native boundary chart and the signed geodesic chart give an
actual product half-space chart. Its smooth metric coefficients in the
orthonormal ambient coordinates have the normalized normal block. -/
theorem exists_nativeBoundaryNormalChart (g : SmoothMetric n M) (p : M)
    (hp : p ∈ (J).boundary M) :
    ∃ (D : ProductBoundaryChart (n := n) (M := M) (Z := XH))
      (G : MetricField n) (e : OpenPartialHomeomorph (X n) (X n)),
      p ∈ D.coord.source ∧ (D.coord p).2 = 0 ∧
      D.ambient = inwardChartSplit.symm ⁻¹' e.source ∧
      D.coord.source = (extChartAt J p).source ∩ (extChartAt J p) ⁻¹' e.target ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      EqOn e id (e.source ∩ {x | x (0 : I n) = 0}) ∧
      (⇑D.coord : M → XH × ℝ) = inwardChartSplit ∘ e.symm ∘ extChartAt J p ∧
      (D.coord.symm : XH × ℝ → M) = (extChartAt J p).symm ∘ e ∘ inwardChartSplit.symm ∧
      EqOn G (chartMetric g p) (e.target ∩ {x | 0 ≤ x (0 : I n)}) ∧
      CalderonN.SmoothMetric e.source (pullbackMetric G e) ∧
      ∀ x ∈ e.source, pullbackMetric G e x 0 0 = 1 ∧
        ∀ j ≠ (0 : I n), pullbackMetric G e x 0 j = 0 := by
  let c := extChartAt J p
  let q := c p
  let L := inwardChartSplit (n := n)
  let H : Set (X n) := {x | 0 ≤ x (0 : I n)}
  have hRange : range ((J) : EuclideanHalfSpace n → X n) = H := range_euclideanHalfSpace n
  have hqc : q ∈ c.target := mem_extChartAt_target p
  have hq0 : q 0 = 0 := by
    have hqb : ¬ 0 < q 0 := by
      intro h
      have hpI : p ∈ (J).interior M := by
        change q ∈ interior (range ((J) : EuclideanHalfSpace n → X n))
        rw [interior_range_modelWithCornersEuclideanHalfSpace]
        exact h
      have hpNot : p ∈ ((J).interior M)ᶜ := by
        rw [(J).compl_interior]
        exact hp
      exact hpNot hpI
    have hh : q ∈ H := by rw [← hRange]; exact extChartAt_target_subset_range p hqc
    exact le_antisymm (le_of_not_gt hqb) hh
  obtain ⟨G,hG,hAgree⟩ := exists_global_metric_germ_of_native_boundaryChart g p hqc hq0
  have hT := extChartAt_target_eventuallyEqSet_of_mem (I := J) hqc
  rw [hRange] at hT
  obtain ⟨V,hVgood,hV,hqV⟩ := _root_.eventually_nhds_iff.mp
    (hT.and (eventually_nhdsWithin_iff.mp hAgree))
  obtain ⟨e,hqe,hRest,hTarget,hE,hEi,hsign,hPull,hBlock⟩ := exists_boundaryNormalMetric hG hq0 hV hqV
  let d₀ := c.trans e.symm.toPartialEquiv
  let d := d₀.transEquiv L.toEquiv
  have hS : d.source = c.source ∩ c ⁻¹' e.target := rfl
  have hTarget₀ : d₀.target = e.source ∩ H := by
    ext x
    change (x ∈ e.source ∧ e x ∈ c.target) ↔ x ∈ e.source ∧ x ∈ H
    constructor
    · rintro ⟨hx,he⟩
      have hVx := hTarget (e.map_source hx)
      exact ⟨hx, (hsign x hx).2.mp ((hVgood _ hVx).1.mp he)⟩
    · rintro ⟨hx,hH⟩
      have hVx := hTarget (e.map_source hx)
      exact ⟨hx, (hVgood _ hVx).1.mpr ((hsign x hx).2.mpr hH)⟩
  let W := L.symm ⁻¹' e.source
  have hW : IsOpen W := e.open_source.preimage L.symm.continuous
  have hDT : d.target = W ∩ (univ ×ˢ Ici (0 : ℝ)) := by
    change L.symm ⁻¹' d₀.target = _
    rw [hTarget₀, preimage_inter]
    congr 1
    ext z
    have hL := inwardChartSplit_height (L.symm z)
    change (L (L.symm z)).2 = _ at hL
    rw [L.apply_symm_apply] at hL
    change 0 ≤ L.symm z 0 ↔ True ∧ 0 ≤ z.2
    rw [← hL, true_and]
  have hDopen : IsOpen d.source := by
    rw [hS]
    exact (continuousOn_extChartAt (I := J) p).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := J) p) e.open_target
  have hDdiff : ContMDiffOn J 𝓘(ℝ, XH × ℝ) ∞ d d.source := by
    change ContMDiffOn J 𝓘(ℝ, XH × ℝ) ∞ (L ∘ e.symm ∘ c) d.source
    refine L.contDiff.contMDiff.comp_contMDiffOn (hEi.contMDiffOn.comp ?_ ?_)
    · exact (contMDiffOn_extChartAt (I := J) (x := p)).mono (fun x hx => by
      have h := (show x ∈ c.source ∩ _ from hx).1
      simpa only [c, extChartAt_source] using h)
    · exact fun _ hx => (show _ ∈ c.source ∩ _ from hx).2
  have hDis : ContMDiffOn 𝓘(ℝ, XH × ℝ) J ∞ d.symm d.target := by
    have hW' : MapsTo L.symm d.target e.source := fun _ hx => (hDT ▸ hx : _ ∈ W ∩ _).1
    have hV' : MapsTo (e ∘ L.symm) d.target c.target := fun x hx =>
      (show L.symm x ∈ e.source ∧ e (L.symm x) ∈ c.target from hx).2
    exact (contMDiffOn_extChartAt_symm (I := J) p).comp
      (hE.contMDiffOn.comp L.symm.contDiff.contMDiff.contMDiffOn hW') hV'
  have hDint (y : M) (hy : y ∈ d.source) : y ∈ (J).interior M ↔ 0 < (d y).2 := by
    have hys : y ∈ c.source ∧ c y ∈ e.target := hy
    have hcV := hTarget hys.2
    have hRel : c.target =ᶠ[𝓝 (c y)] H :=
      Filter.mem_of_superset (hV.mem_nhds hcV) (fun _ hx => (hVgood _ hx).1)
    have h₁ := (J).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas _ p) (by simpa only [c, extChartAt_source] using hys.1)
    change y ∈ (J).interior M ↔ c y ∈ interior c.target at h₁
    have h₂ : e (e.symm (c y)) = c y := e.right_inv hys.2
    have hd : (d y).2 = e.symm (c y) 0 := inwardChartSplit_height _
    rw [h₁, hd, hRel.mem_interior_iff, ← hRange, interior_range_modelWithCornersEuclideanHalfSpace]
    change 0 < c y 0 ↔ 0 < e.symm (c y) 0
    simpa only [h₂] using (hsign _ (e.map_target hys.2)).1
  let D : ProductBoundaryChart (n := n) (M := M) (Z := XH) :=
    ⟨d,hDopen,W,hW,hDT,hDdiff,hDis,hDint⟩
  have hqEq : e q = q := hRest ⟨hqe,hq0⟩
  have hqT : q ∈ e.target := hqEq ▸ e.map_source hqe
  have hdq : e.symm q = q := by conv_lhs => rw [← hqEq, e.left_inv hqe]
  refine ⟨D,G,e,⟨mem_extChartAt_source p,hqT⟩,?_,rfl,hS,hE,hEi,hRest,rfl,rfl,?_,hPull,hBlock⟩
  · change (L (e.symm q)).2 = 0
    rw [hdq, inwardChartSplit_height, hq0]
  · exact fun x hx => (hVgood x (hTarget hx.1)).2 hx.2

end CalderonPatch
