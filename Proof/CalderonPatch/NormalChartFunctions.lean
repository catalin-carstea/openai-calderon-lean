module

public import Proof.CalderonPatch.NativeBoundaryMetricChart

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Proof.CalderonN.ClosedHalfSpaceExtension

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X axis coordDeriv lowerHalfSpace)

private theorem exists_scalar_extension_near_compact {Z : Type}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {U C : Set (Z × ℝ)} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {u : Z × ℝ → ℝ} (hu : ContDiffOn ℝ ∞ u (U ∩ lowerHalfSpace Z)) :
    ∃ (v : Z × ℝ → ℝ) (V : Set (Z × ℝ)), ContDiff ℝ ∞ v ∧ IsOpen V ∧ C ⊆ V ∧
      V ⊆ U ∧ EqOn v u (V ∩ lowerHalfSpace Z) := by
  let S := lowerHalfSpace Z
  obtain ⟨W,hW,hCW,hWU,hWK⟩ := exists_open_between_and_isCompact_closure hC hU hCU
  obtain ⟨V,hV,hCV,hVW,_⟩ := exists_open_between_and_isCompact_closure hC hW hCW
  obtain ⟨χ,hχ,_,hSupp,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hVW
  have hχC : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rw [hSupp]
    exact hWK
  have hχU : tsupport χ ⊆ U := by
    change closure (Function.support χ) ⊆ U
    rwa [hSupp]
  let f : Z × ℝ → ℝ := fun x => χ x * u x
  have hZero {x : Z × ℝ} (hx : x ∉ tsupport (χ : Z × ℝ → ℝ)) :
      f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change χ y = 0 at hy
    simp [f, hy]
  have hf : ContDiffOn ℝ ∞ f S := by
    intro x hx
    by_cases hxU : x ∈ U
    · have h : ContDiffWithinAt ℝ ∞ f (U ∩ S) x :=
        hχ.contDiffAt.contDiffWithinAt.mul (hu x ⟨hxU,hx⟩)
      have hNear : U ∩ S =ᶠ[𝓝 x] S := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        simp [hy]
      exact (contDiffWithinAt_congr_set hNear).mp h
    · exact (contDiffAt_const.congr_of_eventuallyEq (hZero (fun h => hxU (hχU h)))).contDiffWithinAt
  have hSupport (k : ℕ) : HasCompactSupport (fun z : Z =>
      iteratedFDerivWithin ℝ k f S (z,0) (fun _ => (0,1))) := by
    let A := Prod.fst '' tsupport (χ : Z × ℝ → ℝ)
    apply HasCompactSupport.intro (hχC.image continuous_fst)
    intro z hz'
    have hz0 : (z, (0 : ℝ)) ∉ tsupport (χ : Z × ℝ → ℝ) :=
      fun h => hz' (mem_image_of_mem Prod.fst h)
    have h := hZero hz0
    rw [(h.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq h.eq_of_nhds k,
      iteratedFDerivWithin_fun_zero]
    rfl
  obtain ⟨v,hv,hEq⟩ := CalderonN.exists_contDiff_extension_lowerHalfSpace hf hSupport
  refine ⟨v,V,hv,hV,hCV,subset_closure.trans (hVW.trans (subset_closure.trans hWU)),?_⟩
  intro x hx
  rw [hEq hx.2,show f x = χ x * u x from rfl,(hOne x).mp (subset_closure hx.1),one_mul]

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n

omit [T2Space M] [IsManifold J ∞ M] in
/-- A smooth function on the manifold has a signed scalar
representative near compact subsets of a product boundary chart. -/
theorem ProductBoundaryChart.exists_smooth_function_extension {Z : Type}
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (A : ProductBoundaryChart (n := n) (M := M) (Z := Z)) {u : M → ℝ}
    (hu : ContMDiff J 𝓘(ℝ, ℝ) ∞ u)
    {C : Set (Z × ℝ)} (hC : IsCompact C) (hCA : C ⊆ A.ambient) :
    ∃ (v : Z × ℝ → ℝ) (V : Set (Z × ℝ)), ContDiff ℝ ∞ v ∧ IsOpen V ∧ C ⊆ V ∧
      V ⊆ A.ambient ∧ EqOn v (u ∘ A.coord.symm) (V ∩ (univ ×ˢ Ici (0 : ℝ))) := by
  let S : (Z × ℝ) ≃L[ℝ] (Z × ℝ) := ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ Z)
    (ContinuousLinearEquiv.neg ℝ)
  let U := S ⁻¹' A.ambient
  have hU : IsOpen U := A.open_ambient.preimage S.continuous
  have hMap : MapsTo S (U ∩ lowerHalfSpace Z) A.coord.target := by
    intro q hq
    rw [A.target_eq]
    have hLow : q ∈ univ ×ˢ Iic (0 : ℝ) := hq.2
    exact ⟨hq.1,mem_univ _,neg_nonneg.mpr hLow.2⟩
  have hC' : S.symm '' C ⊆ U := by
    rintro _ ⟨q,hq,rfl⟩
    change S (S.symm q) ∈ A.ambient
    rw [S.apply_symm_apply]
    exact hCA hq
  have hRead : ContDiffOn ℝ ∞ (u ∘ A.coord.symm) A.coord.target :=
    (hu.comp_contMDiffOn A.smooth_inverse).contDiffOn
  obtain ⟨v,V,hv,hV,hCV,hVU,hEq⟩ := exists_scalar_extension_near_compact hU
    (hC.image S.symm.continuous) hC' (hRead.comp S.contDiff.contDiffOn hMap)
  refine ⟨v ∘ S.symm,S.symm ⁻¹' V,hv.comp S.symm.contDiff,hV.preimage S.symm.continuous,
    (fun q hq => hCV (mem_image_of_mem _ hq)),?_,?_⟩
  · intro q hq
    have h := hVU hq
    change S (S.symm q) ∈ A.ambient at h
    rwa [S.apply_symm_apply] at h
  · intro q hq
    have hLower : S.symm q ∈ lowerHalfSpace Z := by
      change S.symm q ∈ univ ×ˢ Iic (0 : ℝ)
      refine ⟨mem_univ _,?_⟩
      change -q.2 ≤ 0
      exact neg_nonpos.mpr hq.2.2
    have h := hEq ⟨hq.1,hLower⟩
    change v (S.symm q) = u (A.coord.symm (S (S.symm q))) at h
    rwa [S.apply_symm_apply] at h

omit [T2Space M] in
/-- A smooth function on the original manifold has a globally smooth
signed coordinate representative near any compact part of a normal chart. -/
theorem NativeBoundaryMetricChart.exists_smooth_function_extension
    {g : SmoothMetric n M} {p : M} (D : NativeBoundaryMetricChart g p)
    {u : M → ℝ} (hu : ContMDiff J 𝓘(ℝ, ℝ) ∞ u)
    {C : Set (X n)} (hC : IsCompact C) (hCD : C ⊆ D.ambient) :
    ∃ (v : X n → ℝ) (V : Set (X n)), ContDiff ℝ ∞ v ∧ IsOpen V ∧
      C ⊆ V ∧ V ⊆ D.ambient ∧ EqOn v (u ∘ D.coord.symm) (V ∩ inwardHalfSpace n) := by
  let Z := boundaryTangentPlane (0 : I n)
  let L := boundaryChartSplit (0 : I n)
  let U : Set (Z × ℝ) := L.symm ⁻¹' D.ambient
  let S := lowerHalfSpace Z
  have hU : IsOpen U := D.open_ambient.preimage L.symm.continuous
  have hull : L '' C ⊆ U := by
    rintro _ ⟨x,hx,rfl⟩
    change L.symm (L x) ∈ D.ambient
    rw [L.symm_apply_apply]
    exact hCD hx
  have hMap : MapsTo L.symm (U ∩ S) D.coord.target := by
    intro y hy
    apply D.target_eq.symm ▸ (show L.symm y ∈ D.ambient ∩ inwardHalfSpace n from ⟨hy.1,?_⟩)
    apply (boundaryChartSplit_maps_halfSpace (0 : I n) (L.symm y)).mp
    change L (L.symm y) ∈ S
    rw [L.apply_symm_apply]
    exact hy.2
  have hu' : ContDiffOn ℝ ∞ (u ∘ D.coord.symm) D.coord.target :=
    (hu.comp_contMDiffOn D.smooth_inverse).contDiffOn
  obtain ⟨v,V,hv,hV,hCV,hVU,hEq⟩ := exists_scalar_extension_near_compact
    hU (hC.image L.continuous) hull (hu'.comp L.symm.contDiff.contDiffOn hMap)
  refine ⟨v ∘ L,L ⁻¹' V,hv.comp L.contDiff,hV.preimage L.continuous,?_,?_,?_⟩
  · exact fun x hx => hCV (mem_image_of_mem L hx)
  · intro x hx
    have h := hVU hx
    change L.symm (L x) ∈ D.ambient at h
    rwa [L.symm_apply_apply] at h
  · intro x hx
    have h := hEq ⟨hx.1,(boundaryChartSplit_maps_halfSpace _ _).mpr hx.2⟩
    change v (L x) = u (D.coord.symm (L.symm (L x))) at h
    rwa [L.symm_apply_apply] at h

omit [T2Space M] in
/-- Smooth functions on the original manifold have smooth signed
coordinate germs at every point of a normal boundary face. -/
theorem NativeBoundaryMetricChart.exists_smooth_function_germ {g : SmoothMetric n M} {p : M}
    (D : NativeBoundaryMetricChart g p) {u : M → ℝ} (hu : ContMDiff J 𝓘(ℝ, ℝ) ∞ u) :
    ∃ v : X n → ℝ, ContDiff ℝ ∞ v ∧
      v =ᶠ[𝓝[inwardHalfSpace n] (D.coord p)] u ∘ D.coord.symm := by
  have hx : D.coord p ∈ D.ambient :=
    (D.target_eq ▸ D.coord.map_source D.point_source : _ ∈ D.ambient ∩ _).1
  obtain ⟨v,V,hv,hV,hxV,_,hEq⟩ := D.exists_smooth_function_extension hu
    (isCompact_singleton (x := D.coord p)) (singleton_subset_iff.mpr hx)
  refine ⟨v,hv,?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds (hxV (mem_singleton _))),
    self_mem_nhdsWithin] with y hy hyH
  exact hEq ⟨hy,hyH⟩

omit [T2Space M] in
/-- The inward derivative is the one-sided derivative of the native
coordinate representative in direction zero. -/
def NativeBoundaryMetricChart.inwardDerivative {g : SmoothMetric n M} {p : M}
    (D : NativeBoundaryMetricChart g p) (u : M → ℝ) (x : X n) : ℝ :=
  fderivWithin ℝ (u ∘ D.coord.symm) (inwardHalfSpace n) x (axis (0 : I n))

theorem uniqueDiffOn_inwardHalfSpace : UniqueDiffOn ℝ (inwardHalfSpace n) := by
  have he : inwardHalfSpace n =
      (boundaryChartSplit (0 : I n)) ⁻¹' lowerHalfSpace (boundaryTangentPlane (0 : I n)) := by
    ext x
    exact (boundaryChartSplit_maps_halfSpace (0 : I n) x).symm
  rw [he]
  exact (boundaryChartSplit (0 : I n)).uniqueDiffOn_preimage_iff.mpr CalderonN.uniqueDiffOn_lowerHalfSpace

omit [T2Space M] in
/-- The signed smooth extension computes the intrinsic one-sided
inward derivative on the relative chart germ. -/
theorem NativeBoundaryMetricChart.coordDeriv_eq_inwardDerivative {g : SmoothMetric n M} {p : M}
    (D : NativeBoundaryMetricChart g p) {u : M → ℝ} {a : X n → ℝ}
    (ha : ContDiff ℝ ∞ a)
    (h : a =ᶠ[𝓝[inwardHalfSpace n] (D.coord p)] u ∘ D.coord.symm) :
    coordDeriv 0 a =ᶠ[𝓝[inwardHalfSpace n] (D.coord p)] D.inwardDerivative u := by
  filter_upwards [h.fderivWithin (𝕜 := ℝ),self_mem_nhdsWithin] with z hz hzH
  have ha' := (ha.differentiable (by simp) z).hasFDerivAt
  have hd := ha'.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_inwardHalfSpace z hzH)
  change fderiv ℝ a z (axis (0 : I n)) =
    fderivWithin ℝ (u ∘ D.coord.symm) (inwardHalfSpace n) z (axis (0 : I n))
  rw [← hd,hz]

omit [T2Space M] in
/-- On any open signed neighborhood, the smooth coordinate
representative computes the intrinsic inward derivative. -/
theorem NativeBoundaryMetricChart.inwardDerivative_eq_coordDeriv {g : SmoothMetric n M} {p : M}
    (D : NativeBoundaryMetricChart g p) {U : Set (X n)} (hU : IsOpen U)
    {u : M → ℝ} {a : X n → ℝ} (ha : ContDiffOn ℝ ∞ a U)
    (h : EqOn (u ∘ D.coord.symm) a (U ∩ inwardHalfSpace n)) :
    EqOn (D.inwardDerivative u) (coordDeriv 0 a) (U ∩ inwardHalfSpace n) := by
  intro x hx
  have hNear : u ∘ D.coord.symm =ᶠ[𝓝[inwardHalfSpace n] x] a := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx.1), self_mem_nhdsWithin] with z hzu hzh
    exact h ⟨hzu,hzh⟩
  have hd := ((ha.contDiffAt (hU.mem_nhds hx.1)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_inwardHalfSpace x hx.2)
  change fderivWithin ℝ (u ∘ D.coord.symm) (inwardHalfSpace n) x (axis (0 : I n)) =
    fderiv ℝ a x (axis (0 : I n))
  rw [hNear.fderivWithin_eq_of_mem hx.2,he]

end CalderonPatch
