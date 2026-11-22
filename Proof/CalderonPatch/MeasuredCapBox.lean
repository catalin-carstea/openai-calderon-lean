module

public import Proof.CalderonPatch.SignedCapCoordinates

import Mathlib.Tactic

public section
noncomputable section
open Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ}
local notation "N" => (n+1)
local notation "E" => X N
local notation "Zt" => boundaryTangentPlane (0 : I N)
local notation "L" => (inwardChartSplit (n := N))
local notation "J" => 𝓡∂ N

theorem contDiff_normalFacePoint : ContDiff ℝ ∞ (normalFacePoint (m := n)) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I N => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [Fin.insertNth_apply_same] using (contDiff_const : ContDiff ℝ ∞ (fun _ : X n => (0 : ℝ)))
  · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
    simp only [Fin.insertNth_apply_succAbove]
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff

private theorem push_project_face (z : X n) :
    (inwardChartSplit (n := N)).symm ((L (normalFacePoint z)).1,0) = normalFacePoint z := by
  have h : (L (normalFacePoint z)).2 = 0 := (inwardChartSplit_height _).trans (normalFacePoint_height z)
  rw [← h, Prod.eta, (inwardChartSplit (n := N)).symm_apply_apply]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
  [MeasurableSpace M]
  {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}

namespace MeasuredCommonCap

variable (C : MeasuredCommonCap d₁ d₂ Γ)


/-- The compact cap-gluing box in Euclidean coordinates. -/
@[expose] def signedBox : Set E := WithLp.toLp 2 '' Icc C.coordinates.box.lower C.coordinates.box.upper

/-- The open signed chart shared by the two original collars. -/
@[expose] def signedRegion : Set E := L ⁻¹' C.ambient

/-- Height of the pushed cap expressed in the Euclidean tangential
coordinates of the measured boundary. -/
@[expose] def signedHeight (z : X n) : ℝ := C.coordinates.height (L (normalFacePoint z)).1

theorem signedHeight_contDiff : ContDiff ℝ ∞ C.signedHeight :=
  C.coordinates.smooth_height.comp (contDiff_fst.comp
    ((inwardChartSplit (n := N)).contDiff.comp contDiff_normalFacePoint))

theorem signedHeight_read (x : E) :
    C.signedHeight (normalTangentialCoordinates x) = C.coordinates.height (L x).1 := by
  unfold signedHeight
  rw [← inwardChartSplit_fst_eq_normalFacePoint]

theorem signedHeight_bounds (z : X n) :
    0 ≤ C.signedHeight z ∧ C.coordinates.box.lower 0 < -C.signedHeight z :=
  ⟨(C.coordinates.height_bound _).1,C.coordinates.box.bottom_lt.trans (neg_lt_neg (C.coordinates.height_bound _).2)⟩

theorem isCompact_signedBox : IsCompact C.signedBox :=
  isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : I N => ℝ))

theorem isOpen_signedRegion : IsOpen C.signedRegion :=
  C.open_ambient.preimage (inwardChartSplit (n := N)).continuous

theorem signedBox_subset : C.signedBox ⊆ C.signedRegion := by
  rintro _ ⟨x,hx,rfl⟩
  exact C.coordinates.box.box_inside hx

theorem signedCap_push_iff (x : E) :
    C.coordinates.push (L x) ∈ pushedCap C.coordinates.height ↔ x ∈ signedCap C.signedHeight := by
  let e := C.coordinates.push
  let z := (L x).1
  let t := (L x).2
  have h₁ : (e (z,-C.coordinates.height z)).2 = 0 :=
    congrArg Prod.snd (C.coordinates.push_boundary z)
  have h₂ : (e (z,0)).2 = C.coordinates.height z :=
    congrArg Prod.snd (C.coordinates.push_seam z)
  have hStrict : StrictMono (fun t : ℝ => (e (z,t)).2) := C.coordinates.push_monotone z
  have heq : C.coordinates.push (L x) = e (z,t) := rfl
  change (0 < (C.coordinates.push (L x)).2 ∧
      (C.coordinates.push (L x)).2 < C.coordinates.height (C.coordinates.push (L x)).1) ↔
    -C.signedHeight (normalTangentialCoordinates x) < x 0 ∧ x 0 < 0
  rw [C.coordinates.push_tangential,C.signedHeight_read,← inwardChartSplit_height x,heq]
  have hLo : 0 < (e (z,t)).2 ↔ -C.coordinates.height z < t := by
    simpa only [h₁] using (hStrict.lt_iff_lt (a := -C.coordinates.height z) (b := t))
  have hHi : (e (z,t)).2 < C.coordinates.height z ↔ t < 0 := by
    simpa only [h₂] using (hStrict.lt_iff_lt (a := t) (b := 0))
  exact and_congr hLo hHi

theorem signedCap_subset_box : signedCap C.signedHeight ⊆ C.signedBox := by
  intro x hx
  have hx₁ : -C.signedHeight (normalTangentialCoordinates x) < x 0 := hx.1
  have hx₂ : x 0 < 0 := hx.2
  rw [C.signedHeight_read] at hx₁
  have hxpos : 0 < C.coordinates.height (L x).1 := by linarith
  have hBall : (L x).1 ∈ closedBall (C.charts.prod₂.coord C.center).1 C.coordinates.box.radius :=
    ball_subset_closedBall (C.coordinates.height_support ▸ hxpos)
  have hLine : (L x).2 ∈ Icc (-C.coordinates.box.radius) C.coordinates.box.radius := by
    rw [inwardChartSplit_height]
    have hR := (C.coordinates.height_bound (L x).1).2
    have hRp := C.coordinates.box.radius_pos
    constructor <;> linarith
  have hBox := C.coordinates.box.push_inside ⟨hBall,hLine⟩
  rw [Function.comp_apply,(inwardChartSplit (n := N)).symm_apply_apply] at hBox
  refine ⟨WithLp.ofLp x,⟨?_,?_⟩,WithLp.toLp_ofLp _ _⟩
  · intro i
    exact ((Set.mem_pi.mp hBox) i (mem_univ i)).1.le
  · intro i
    exact ((Set.mem_pi.mp hBox) i (mem_univ i)).2.le

theorem isOpen_signedCap : IsOpen (signedCap C.signedHeight) :=
  (isOpen_lt (C.signedHeight_contDiff.continuous.comp
      contDiff_normalTangentialCoordinates.continuous).neg
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : I N)).continuous).inter
    (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (0 : I N)).continuous continuous_const)

/-- The tangential projection of the push support is compact and
strictly inside the sides of the common box. -/
theorem exists_compact_signedHeight_support :
    ∃ Q : Set (X n), IsCompact Q ∧ Function.support C.signedHeight ⊆ Q ∧
      Q ⊆ tangentialBox C.coordinates.box.lower C.coordinates.box.upper := by
  let f (q : Zt) := normalTangentialCoordinates ((inwardChartSplit (n := N)).symm (q,0))
  let U := closedBall (C.charts.prod₂.coord C.center).1 C.coordinates.box.radius
  have hf : Continuous f := contDiff_normalTangentialCoordinates.continuous.comp
    ((inwardChartSplit (n := N)).symm.continuous.comp (continuous_id.prodMk continuous_const))
  refine ⟨f '' U,(isCompact_closedBall _ _).image hf,?_,?_⟩
  · intro z hz
    refine ⟨(L (normalFacePoint z)).1,?_,?_⟩
    · have hne : C.coordinates.height (L (normalFacePoint z)).1 ≠ 0 := hz
      have hPos : 0 < C.coordinates.height (L (normalFacePoint z)).1 :=
        lt_of_le_of_ne (C.coordinates.height_bound _).1 (Ne.symm hne)
      exact ball_subset_closedBall (C.coordinates.height_support ▸ hPos)
    · change normalTangentialCoordinates ((inwardChartSplit (n := N)).symm
        ((L (normalFacePoint z)).1,0)) = z
      rw [push_project_face,normalTangentialCoordinates_facePoint]
  · rintro _ ⟨q,hq,rfl⟩ i
    have ht : (0 : ℝ) ∈ Icc (-C.coordinates.box.radius) C.coordinates.box.radius :=
      ⟨neg_nonpos.mpr C.coordinates.box.radius_pos.le,C.coordinates.box.radius_pos.le⟩
    have h := Set.mem_pi.mp (C.coordinates.box.push_inside (show (q,0) ∈ U ×ˢ Icc (-C.coordinates.box.radius) C.coordinates.box.radius
      from ⟨hq,ht⟩)) ((0 : I N).succAbove i) (mem_univ _)
    exact h

/-- The inward half of the signed cap box. -/
@[expose] def originalLower : I N → ℝ := Function.update C.coordinates.box.lower 0 0

/-- The upper bounds of the exterior half of the signed cap box. -/
@[expose] def capUpper : I N → ℝ := Function.update C.coordinates.box.upper 0 0

@[simp] theorem originalLower_normal : C.originalLower 0 = 0 := by simp [originalLower]
@[simp] theorem capUpper_normal : C.capUpper 0 = 0 := by simp [capUpper]

theorem originalLower_le : C.originalLower ≤ C.coordinates.box.upper := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [C.originalLower_normal]
    exact C.coordinates.box.radius_pos.le.trans C.coordinates.box.top_lt.le
  · simpa [originalLower,Function.update_of_ne hi] using C.coordinates.box.bounds i

theorem lower_le_capUpper : C.coordinates.box.lower ≤ C.capUpper := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [C.capUpper_normal]
    exact C.coordinates.box.bottom_lt.le.trans (neg_nonpos.mpr C.coordinates.box.radius_pos.le)
  · simpa [capUpper,Function.update_of_ne hi] using C.coordinates.box.bounds i

theorem mapsTo_originalBox {U : Set E} (hU : C.signedBox ⊆ U) :
    MapsTo (WithLp.toLp 2) (Icc C.originalLower C.coordinates.box.upper) U := by
  intro x hx
  apply hU
  refine ⟨x,⟨fun i => ?_,hx.2⟩,rfl⟩
  apply (show C.coordinates.box.lower i ≤ C.originalLower i by
    by_cases hi : i = 0
    · subst i
      rw [C.originalLower_normal]
      exact C.coordinates.box.bottom_lt.le.trans (neg_nonpos.mpr C.coordinates.box.radius_pos.le)
    · simp [originalLower, Function.update_of_ne hi]).trans (hx.1 i)

theorem mapsTo_capBox {U : Set E} (hU : C.signedBox ⊆ U) :
    MapsTo (WithLp.toLp 2) (Icc C.coordinates.box.lower C.capUpper) U := by
  intro x hx
  apply hU
  refine ⟨x,⟨hx.1,fun i => ?_⟩,rfl⟩
  apply (hx.2 i).trans (show C.capUpper i ≤ C.coordinates.box.upper i by
    by_cases hi : i = 0
    · subst i
      rw [C.capUpper_normal]
      exact C.coordinates.box.radius_pos.le.trans C.coordinates.box.top_lt.le
    · simp [capUpper,Function.update_of_ne hi])

theorem tangentialBox_original : tangentialBox C.originalLower C.coordinates.box.upper = tangentialBox C.coordinates.box.lower C.coordinates.box.upper := by
  ext z
  simp [tangentialBox,originalLower]

theorem tangentialBox_cap : tangentialBox C.coordinates.box.lower C.capUpper = tangentialBox C.coordinates.box.lower C.coordinates.box.upper := by
  ext z
  simp [tangentialBox,capUpper]

theorem capUpper_tangential :
    C.capUpper ∘ Fin.succAbove 0 = C.coordinates.box.upper ∘ Fin.succAbove 0 := by
  funext i
  simp [capUpper]

end MeasuredCommonCap

end CalderonPatch
