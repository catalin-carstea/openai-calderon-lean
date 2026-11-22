module

public import Proof.CalderonPatch.MeasuredCapReadings

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic

public section
noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (n+1)
local notation "E" => X N
local notation "Zt" => boundaryTangentPlane (0 : I N)
local notation "L" => (inwardChartSplit (n := N))
local notation "J" => 𝓡∂ N
local notation "H" => inwardHalfSpace N

variable {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}
  {C : MeasuredCommonCap d₁ d₂ Γ}

namespace MeasuredCommonCap

omit [T2Space M] [CompactSpace M] [BorelSpace M] [PreconnectedSpace M] in
private theorem point_on_signedBox_of_touching
    (A : ProductBoundaryChart (n := N) (M := M) (Z := Zt))
    {g : SmoothMetric N M} {p₀ : M} (D : NativeBoundaryMetricChart g p₀)
    (hInv : ∀ x ∈ C.signedRegion ∩ H, D.coord.symm x = A.coord.symm (L x))
    {p : M} (hp : p ∈ (J).boundary M)
    (hTouch : p ∈ A.coord.source ∧ C.coordinates.height (A.coord p).1 ≠ 0) :
    ∃ x ∈ C.signedBox, x 0 = 0 ∧ D.coord.symm x = p := by
  let y := A.coord p
  let x := (inwardChartSplit (n := N)).symm y
  have hY : y.2 = 0 := A.height_eq_zero_on_boundary hp hTouch.1
  have hx₀ : x 0 = 0 := (inwardChartSplit_symm_height y).trans hY
  have hPos : 0 < C.coordinates.height y.1 :=
    lt_of_le_of_ne (C.coordinates.height_bound _).1 (Ne.symm hTouch.2)
  have hXY : L x = y := (inwardChartSplit (n := N)).apply_symm_apply y
  have hb : y.1 ∈ closedBall (C.charts.prod₂.coord C.center).1 C.coordinates.box.radius :=
    ball_subset_closedBall (C.coordinates.height_support ▸ hPos)
  have hr := C.coordinates.box.radius_pos.le
  have hT : y.2 ∈ Icc (-C.coordinates.box.radius) C.coordinates.box.radius := by
    rw [hY]
    exact ⟨neg_nonpos.mpr hr,hr⟩
  have h := Set.mem_pi.mp (C.coordinates.box.push_inside ⟨hb,hT⟩)
  have hB : x ∈ C.signedBox := ⟨WithLp.ofLp x,⟨fun i => (h i (mem_univ i)).1.le,
    fun i => (h i (mem_univ i)).2.le⟩,WithLp.toLp_ofLp _ _⟩
  refine ⟨x,hB,hx₀,?_⟩
  rw [hInv x ⟨C.signedBox_subset hB,(mem_inwardHalfSpace).mpr hx₀.ge⟩,hXY]
  exact A.coord.left_inv hTouch.1

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] in
private theorem nativeFaceTraceDoesNotSeeOutside
    {U : Set E} {g : SmoothMetric N M} {p₀ : M} (D : NativeBoundaryMetricChart g p₀)
    {a b : I N → ℝ} (ha : a 0 = 0) (hUD : U ⊆ D.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U)
    {f : E → ℝ} (hfC : HasCompactSupport f) (hfS : tsupport f ∩ H ⊆ normalHalfBox a b)
    {p : M} (hp : p ∈ (J).boundary M)
    (hOut : ¬∃ x ∈ U, x 0 = 0 ∧ D.coord.symm x = p) :
    boundaryChartTest D f p = 0 := by
  by_contra hn
  have hS := tsupport_boundaryChartTest_subset_halfBox D ha (hBox.mono_right hUD) hfC hfS
    (subset_closure (show p ∈ Function.support (boundaryChartTest D f) from hn))
  have hx := hBox (normalHalfBox_subset_closedBox ha hS.2)
  rw [WithLp.toLp_ofLp] at hx
  exact hOut ⟨D.coord p,hx,D.coord_height_eq_zero hS.1 hp,D.coord.left_inv hS.1⟩

omit [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] in
private theorem addFaceCoordinateTrace
    {g : SmoothMetric N M} {p₀ : M} (D : NativeBoundaryMetricChart g p₀)
    {f : E → ℝ} {φ : X n → ℝ} (hfT : f ∘ normalFacePoint = φ)
    {x : E} (hx : x ∈ D.ambient) (hx₀ : x 0 = 0) :
    boundaryChartTest D f (D.coord.symm x) = φ (normalTangentialCoordinates x) := by
  have hT : x ∈ D.coord.target := D.target_eq.symm ▸ ⟨hx,(mem_inwardHalfSpace).mpr hx₀.ge⟩
  rw [show boundaryChartTest D f (D.coord.symm x) = f x from boundaryChartTest_comp_inverse D f hT,
    ← congrFun hfT (normalTangentialCoordinates x),Function.comp_apply,
    normalFacePoint_tangentialCoordinates hx₀]

omit [CompactSpace M] [BorelSpace M] [PreconnectedSpace M] in
/-- A smooth test for the truncated difference of the two cap traces.
The same signed test gives the two supported native boundary readings. -/
theorem ScalarReadings.exists_truncated_trace_test
    {w₁ w₂ : M → ℝ} (D : C.ScalarReadings w₁ w₂)
    (hw₁ : EqOn w₁ 0 ((J).boundary M)) (hw₂ : EqOn w₂ 0 ((J).boundary M))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : E → ℝ) (φ : X n → ℝ), ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ∩ H ⊆ normalHalfBox C.originalLower C.coordinates.box.upper ∧
      f ∘ normalFacePoint = φ ∧
      (∀ z, normalFacePoint z ∈ D.domain →
        φ z = capTraceCutoff ε ((D.first-D.second) (normalFacePoint z))) ∧
      EqOn (boundaryChartTest C.charts.first f)
        (capTraceCutoff ε ∘ ((w₁ ∘ C.firstCopy.embed) - (w₂ ∘ C.secondCopy.embed))) ((J).boundary M) ∧
      EqOn (boundaryChartTest C.charts.second f)
        (capTraceCutoff ε ∘ ((w₁ ∘ C.firstCopy.embed) - (w₂ ∘ C.secondCopy.embed))) ((J).boundary M) := by
  let a := C.originalLower
  let b := C.coordinates.box.upper
  let S := tangentialBox a b
  have hS : IsOpen S := isOpen_tangentialBox _ _
  obtain ⟨Q,hQ,hSupp,hQS⟩ := C.exists_compact_signedHeight_support
  have hQS' : Q ⊆ S := by rwa [show S = _ from C.tangentialBox_original]
  obtain ⟨U,hU,hQU,hUS,hUC⟩ := exists_open_between_and_isCompact_closure hQ hS hQS'
  obtain ⟨χ,hχ,_,hχSupp,hχOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU hQ.isClosed hQU
  let φ (z : X n) := χ z * capTraceCutoff ε ((D.first-D.second) (normalFacePoint z))
  have hφ : ContDiff ℝ ∞ φ := hχ.mul ((capTraceCutoff_contDiff ε).comp
    ((D.smooth_first.sub D.smooth_second).comp contDiff_normalFacePoint))
  have hφs : tsupport φ ⊆ closure U := by
    apply closure_minimal _ isClosed_closure
    intro z hz
    have hχz : χ z ≠ 0 := by
      intro he
      apply hz
      change χ z * _ = _
      rw [he,zero_mul]
    exact subset_closure (hχSupp ▸ hχz)
  have hφc : HasCompactSupport φ := hUC.of_isClosed_subset (isClosed_tsupport φ) hφs
  have hφRead (z : X n) (hz : normalFacePoint z ∈ D.domain) :
      φ z = capTraceCutoff ε ((D.first-D.second) (normalFacePoint z)) := by
    by_cases h : z ∈ Q
    · change χ z * _ = _
      rw [(hχOne z).mp h,one_mul]
    · have hHeight : C.signedHeight z = 0 := not_not.mp (fun hz' => h (hSupp hz'))
      have h0 := D.sub_zero_on_graph hw₁ hw₂ hz (by
        rw [normalFacePoint_height,normalTangentialCoordinates_facePoint,hHeight,neg_zero])
      have hKzero : capTraceCutoff ε 0 = 0 :=
        capTraceCutoff_zero_of_abs_le hε (by simpa using hε.le)
      change χ z * capTraceCutoff ε ((D.first-D.second) (normalFacePoint z)) = _
      rw [h0,hKzero,mul_zero]
  obtain ⟨f,hf,hfC,hfS,hfT⟩ := exists_halfBoxTest
    (C.coordinates.box.radius_pos.trans C.coordinates.box.top_lt) hφ hφc (hφs.trans hUS)
  refine ⟨f,φ,hf,hfC,hfS,hfT,hφRead,?_⟩
  let v₁ := w₁ ∘ C.firstCopy.embed
  let v₂ := w₂ ∘ C.secondCopy.embed
  let faceDom := D.domain ∩ {x : E | x 0 = 0}
  have hFirst : D.domain ⊆ C.charts.first.ambient := D.domain_subset.trans C.nativeAmbient_first
  have hSecond : D.domain ⊆ C.charts.second.ambient := D.domain_subset.trans C.nativeAmbient_second
  have hBox := C.mapsTo_originalBox D.box_subset
  have hCommon (x : E) (hx : x ∈ faceDom) :
      C.charts.first.coord.symm x = C.charts.second.coord.symm x :=
    C.nativeFaceInverse_eq (D.domain_subset hx.1) hx.2
  have hRead (p : M) (x : E) (hx : x ∈ faceDom)
      (hp : C.charts.first.coord.symm x = p) :
      φ (normalTangentialCoordinates x) = (capTraceCutoff ε ∘ (v₁-v₂)) p := by
    have hxH : x ∈ H := (mem_inwardHalfSpace).mpr hx.2.ge
    have h₁ : v₁ p = D.first x := by
      rw [← hp]
      exact D.original_first ⟨hx.1,hxH⟩
    have h₂ : v₂ p = D.second x := by
      rw [← hp,hCommon x hx]
      exact D.original_second ⟨hx.1,hxH⟩
    have hZ := normalFacePoint_tangentialCoordinates hx.2
    rw [hφRead _ (hZ.symm ▸ hx.1),hZ]
    change capTraceCutoff ε (D.first x - D.second x) = capTraceCutoff ε (v₁ p - v₂ p)
    rw [h₁,h₂]
  have hOutside (p : M) (hp : p ∈ (J).boundary M)
      (hOut : ¬∃ x ∈ faceDom, C.charts.first.coord.symm x = p) :
      v₁ p = 0 ∧ v₂ p = 0 := by
    constructor
    · apply C.coordinates.first.original_boundary_zero_of_not_touching C.coordinates.push_seam hw₁ hp
      intro hT
      obtain ⟨x,hB,hx₀,he⟩ := point_on_signedBox_of_touching C.productFirst C.charts.first
        (fun _ hx => C.chartInverse_first hx) hp hT
      exact hOut ⟨x,⟨D.box_subset hB,hx₀⟩,he⟩
    · apply C.coordinates.second.original_boundary_zero_of_not_touching C.coordinates.push_seam hw₂ hp
      intro hT
      obtain ⟨x,hB,hx₀,he⟩ := point_on_signedBox_of_touching C.productSecond C.charts.second
        (fun _ hx => C.chartInverse_second hx) hp hT
      have hx : x ∈ faceDom := ⟨D.box_subset hB,hx₀⟩
      exact hOut ⟨x,hx,(hCommon x hx).trans he⟩
  have hBoth (p : M) (hp : p ∈ (J).boundary M) :
      boundaryChartTest C.charts.first f p = (capTraceCutoff ε ∘ (v₁-v₂)) p ∧
      boundaryChartTest C.charts.second f p = (capTraceCutoff ε ∘ (v₁-v₂)) p := by
    by_cases h : ∃ x ∈ faceDom, C.charts.first.coord.symm x = p
    · obtain ⟨x,hx,he⟩ := h
      have he₂ := (hCommon x hx).symm.trans he
      constructor
      · rw [← he]
        exact (addFaceCoordinateTrace C.charts.first hfT (hFirst hx.1) hx.2).trans (hRead _ x hx rfl)
      · have hR := hRead p x hx he
        rw [← he₂]
        exact (addFaceCoordinateTrace C.charts.second hfT (hSecond hx.1) hx.2).trans (he₂.symm ▸ hR)
    · have hV := hOutside p hp h
      have h0 : (capTraceCutoff ε ∘ (v₁-v₂)) p = 0 := by
        change capTraceCutoff ε (v₁ p-v₂ p) = 0
        rw [hV.1,hV.2,sub_zero]
        exact capTraceCutoff_zero_of_abs_le hε (by simpa using hε.le)
      rw [h0]
      constructor
      · apply nativeFaceTraceDoesNotSeeOutside C.charts.first C.originalLower_normal hFirst hBox hfC hfS hp
        rintro ⟨x,hx,hx₀,he⟩
        exact h ⟨x,⟨hx,hx₀⟩,he⟩
      · apply nativeFaceTraceDoesNotSeeOutside C.charts.second C.originalLower_normal hSecond hBox hfC hfS hp
        rintro ⟨x,hx,hx₀,he⟩
        exact h ⟨x,⟨hx,hx₀⟩,(hCommon x ⟨hx,hx₀⟩).trans he⟩
  exact ⟨fun p hp => (hBoth p hp).1,fun p hp => (hBoth p hp).2⟩

end MeasuredCommonCap

end CalderonPatch
