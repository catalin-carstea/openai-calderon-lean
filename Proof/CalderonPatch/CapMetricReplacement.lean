module

public import Proof.CalderonPatch.NativeMetricPatch
public import Proof.CalderonPatch.NormalMetricRealization
public import Proof.CalderonPatch.ReturnToOriginal

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField metricPair)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "T" => TangentSpace J
local notation "Tangential" => boundaryTangentPlane (0 : I n)
local notation "P" => 𝓘(ℝ, Tangential × ℝ)

private theorem mfderiv_injective_of_productBoundaryChart
    (D : ProductBoundaryChart (n := n) (M := M) (Z := Tangential)) {x : M} (hx : x ∈ D.coord.source) :
    Function.Injective (mfderiv J P D.coord x) := by
  have hC := (D.smooth.contMDiffAt (D.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hCi := (D.smooth_inverse (D.coord x) (D.coord.map_source hx)).mdifferentiableWithinAt (by simp)
  have hw := mfderivWithin_comp x hCi hC.mdifferentiableWithinAt
    (fun _ hy => D.coord.map_source hy) (D.open_source.uniqueMDiffOn x hx)
  rw [mfderivWithin_of_isOpen D.open_source hx, mfderivWithin_of_isOpen D.open_source hx] at hw
  have hId : (D.coord.symm : Tangential × ℝ → M) ∘ D.coord =ᶠ[𝓝 x] id :=
    Filter.mem_of_superset (D.open_source.mem_nhds hx) (fun _ hy => D.coord.left_inv hy)
  rw [hId.mfderiv_eq, mfderiv_id] at hw
  intro a b h
  have hh := congrArg (mfderivWithin P J D.coord.symm D.coord.target (D.coord x)) h
  change ((mfderivWithin P J D.coord.symm D.coord.target (D.coord x)).comp
    (mfderiv J P D.coord x)) a = _ at hh
  have hh' := DFunLike.congr_fun hw a
  have hh'' := DFunLike.congr_fun hw b
  exact hh'.trans (hh.trans hh''.symm)

private theorem mfderiv_injective_of_smoothEquiv {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {e : E ≃ E'} (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (x : E) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') e x) := by
  have hd := (he.differentiable (by simp) x).hasFDerivAt
  have hdi := (hei.differentiable (by simp) (e x)).hasFDerivAt
  have hc : (e.symm : E' → E) ∘ e = id := funext e.symm_apply_apply
  have h := hdi.comp x hd
  rw [hc] at h
  have hInv := h.unique (hasFDerivAt_id x)
  let A : E →L[ℝ] E' := fderiv ℝ e x
  let B : E' →L[ℝ] E := fderiv ℝ e.symm (e x)
  have hI : B.comp A = ContinuousLinearMap.id ℝ E := hInv
  have hA : Function.Injective A := by
    intro u v huv
    have h := congrArg B huv
    change (B.comp A) u = (B.comp A) v at h
    rwa [hI] at h
  rw [mfderiv_eq_fderiv]
  exact hA

/-- A prescribed smooth signed extension of the coordinate metric
gives a native Riemannian extension. The shifted map embeds the
original isometrically and the new metric agrees with the original
away from the compactly supported cap change. -/
theorem exists_originalCopy_of_capShift
    (g : SmoothMetric n M) (D : ProductBoundaryChart (n := n) (M := M) (Z := Tangential)) (C : CapShift D)
    {γ γe : MetricField n}
    (hγe : CalderonN.SmoothMetric (inwardChartSplit ⁻¹' D.ambient) γe)
    (hInward : EqOn γe γ ((inwardChartSplit ⁻¹' D.ambient) ∩ {x | 0 ≤ x (0 : I n)}))
    (hNative : ∀ x ∈ D.coord.source,
      nativeCoordinateBilinear γ (inwardChartSplit.symm ∘ D.coord) x = g.inner x) :
    ∃ (gExt : SmoothMetric n M) (O : OriginalCopy g gExt C.cap),
      O.embed = C.embed ∧
      ∀ x ∈ D.coord.source, gExt.inner x =
        nativeCoordinateBilinear γe (inwardChartSplit.symm ∘ C.coordinateShift.symm ∘ D.coord) x := by
  let L := inwardChartSplit (n := n)
  let a : M → X n := L.symm ∘ D.coord
  let q : M → X n := L.symm ∘ C.coordinateShift.symm ∘ D.coord
  let U := L ⁻¹' D.ambient
  have hEa : ContMDiffOn J K ∞ a D.coord.source := L.symm.contDiff.contMDiff.comp_contMDiffOn D.smooth
  have hEs : ContMDiff P P ∞ C.coordinateShift.symm := C.smooth_coordinateShift_inverse.contMDiff
  have hEq : ContMDiffOn J K ∞ q D.coord.source :=
    L.symm.contDiff.contMDiff.comp_contMDiffOn (hEs.comp_contMDiffOn D.smooth)
  have hW (x : M) (hx : x ∈ D.coord.source) : D.coord x ∈ D.ambient :=
    (D.target_eq ▸ D.coord.map_source hx : _ ∈ D.ambient ∩ _).1
  have hQ (x : M) (hx : x ∈ D.coord.source) : q x ∈ U := by
    change L (L.symm (C.coordinateShift.symm (D.coord x))) ∈ D.ambient
    rw [L.apply_symm_apply]
    apply (C.coordinateShift_ambient _).mp
    rw [C.coordinateShift.apply_symm_apply]
    exact hW x hx
  have hA (x : M) (hx : x ∈ D.coord.source) : a x ∈ U ∩ {x | 0 ≤ x (0 : I n)} := by
    refine ⟨?_, ?_⟩
    · change L (L.symm (D.coord x)) ∈ D.ambient
      rw [L.apply_symm_apply]
      exact hW x hx
    · change 0 ≤ L.symm (D.coord x) 0
      rw [← inwardChartSplit_height]
      change 0 ≤ (L (L.symm (D.coord x))).2
      rw [L.apply_symm_apply]
      exact (D.target_eq ▸ D.coord.map_source hx : _ ∈ D.ambient ∩ _).2.2
  have hRank (x : M) (hx : x ∈ D.coord.source) : Function.Injective (mfderiv J K q x) := by
    have hDc := (D.smooth.contMDiffAt (D.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
    have hDs := hEs.mdifferentiable (by simp) (D.coord x)
    have hL : ContMDiff P K ∞ L.symm := L.symm.contDiff.contMDiff
    have hDl := hL.mdifferentiable (by simp) (C.coordinateShift.symm (D.coord x))
    have hc₁ := mfderiv_comp x hDl (hDs.comp x hDc)
    have hc₂ := mfderiv_comp x hDs hDc
    change mfderiv J K q x = _ at hc₁
    rw [hc₁, hc₂]
    exact ((mfderiv_injective_of_smoothEquiv (e := L.symm.toEquiv) L.symm.contDiff L.contDiff _).comp
      ((mfderiv_injective_of_smoothEquiv C.smooth_coordinateShift_inverse C.smooth_coordinateShift _).comp
        (mfderiv_injective_of_productBoundaryChart D hx)))
  have hOff (x : M) (hx : x ∈ D.coord.source \ C.support) : q x = a x := by
    have hh := (C.coordinateShift_spec x hx.1).2
    have hE : C.embed x = x := C.embed_eq_id_off_support hx.2
    rw [hE] at hh
    change L.symm (C.coordinateShift.symm (D.coord x)) = L.symm (D.coord x)
    conv_lhs => rw [hh, C.coordinateShift.symm_apply_apply]
  have hMetricOff (x : M) (hx : x ∈ D.coord.source \ C.support) :
      nativeCoordinateBilinear γe q x = g.inner x := by
    have hNear : q =ᶠ[𝓝 x] a :=
      Filter.mem_of_superset ((D.open_source.sdiff C.closed_support).mem_nhds hx) hOff
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    have hm := congrArg (fun B : T x →L[ℝ] T x →L[ℝ] ℝ => B v w) (hNative x hx.1)
    rw [nativeCoordinateBilinear_apply] at hm ⊢
    let A : T x →L[ℝ] X n := mfderiv J K a x
    let Q : T x →L[ℝ] X n := mfderiv J K q x
    have hrd : Q = A := hNear.mfderiv_eq
    change metricPair γ (a x) (A v) (A w) = _ at hm
    change metricPair γe (q x) (Q v) (Q w) = _
    rw [hNear.eq_of_nhds, hrd, ← hm]
    have heq : γe (a x) = γ (a x) := hInward (hA x hx.1)
    simp only [metricPair, heq]
  obtain ⟨gExt,hExt,hExtOff⟩ := exists_nativeMetric_of_coordinate_replacement g D.open_source
    C.closed_support C.support_in_chart hγe hEq hQ hRank hMetricOff
  have hMetric (x : M) (v w : T x) : g.inner x v w =
      gExt.inner (C.embed x) (mfderiv J J C.embed x v) (mfderiv J J C.embed x w) := by
    by_cases hx : x ∈ D.coord.source
    · have hEmb (y : M) (hy : y ∈ D.coord.source) : (q ∘ C.embed) y = a y := by
        change L.symm (C.coordinateShift.symm (D.coord (C.embed y))) = L.symm (D.coord y)
        rw [(C.coordinateShift_spec y hy).2, C.coordinateShift.symm_apply_apply]
      have hEqa : q ∘ C.embed =ᶠ[𝓝 x] a :=
        Filter.mem_of_superset (D.open_source.mem_nhds hx) hEmb
      have hyn := (C.coordinateShift_spec x hx).1
      have hMd := (hEq.contMDiffAt (D.open_source.mem_nhds hyn)).mdifferentiableAt (by simp)
      have hDer := mfderiv_comp x hMd (C.smooth.mdifferentiable (by simp) x)
      rw [hEqa.mfderiv_eq] at hDer
      have hvec (s : T x) : mfderiv J K q (C.embed x) (mfderiv J J C.embed x s) = mfderiv J K a x s :=
        (DFunLike.congr_fun hDer s).symm
      rw [hExt _ hyn, nativeCoordinateBilinear_apply, hvec v, hvec w]
      change _ = metricPair γe ((q ∘ C.embed) x) _ _
      rw [hEqa.eq_of_nhds]
      have heq : γe (a x) = γ (a x) := hInward (hA x hx)
      have hN := congrArg (fun B : T x →L[ℝ] T x →L[ℝ] ℝ => B v w) (hNative x hx)
      rw [nativeCoordinateBilinear_apply] at hN
      change metricPair γ (a x) (mfderiv J K a x v) (mfderiv J K a x w) = _ at hN
      rw [← hN]
      simp only [metricPair, heq]
    · have hNot : x ∉ C.support := fun h => hx (C.support_in_chart h)
      have hEff : C.embed =ᶠ[𝓝 x] id :=
        Filter.mem_of_superset (C.closed_support.isOpen_compl.mem_nhds hNot) C.embed_eq_id_off_support
      have hxx : C.embed x = x := hEff.eq_of_nhds
      have hDx : mfderiv J J C.embed x = ContinuousLinearMap.id ℝ (T x) :=
        hEff.mfderiv_eq.trans (mfderiv_id (I := J))
      have hInn : gExt.inner (C.embed x) (v : X n) (w : X n) = g.inner x v w := by
        exact (congrArg (fun y => gExt.inner y (v : X n) (w : X n)) hxx).trans
          (congrArg (fun B : T x →L[ℝ] T x →L[ℝ] ℝ => B v w) (hExtOff x hNot))
      exact hInn.symm.trans (by rw [hDx]; rfl)
  let O : OriginalCopy g gExt C.cap :=
    ⟨C.embed,C.inverse,C.left_inv,C.smooth,C.smooth_inverse,C.interior_image,hMetric⟩
  exact ⟨gExt,O,rfl,hExt⟩

end CalderonPatch
