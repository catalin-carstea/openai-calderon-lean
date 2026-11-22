module

public import Proof.CalderonPatch.MeasuredCommonCap
public import Proof.CalderonPatch.CapFluxComparison
public import Proof.CalderonPatch.NativeLaplace

import Mathlib.Tactic

public section
noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X axis metricPair MetricField)

variable {n : ℕ}
local notation "N" => (n+1)
local notation "E" => X N
local notation "Zt" => boundaryTangentPlane (0 : I N)
local notation "L" => (inwardChartSplit (n := N))
local notation "J" => 𝓡∂ N
local notation "K" => 𝓘(ℝ, X N)

theorem inwardChartSplit_fst_eq_normalFacePoint (x : E) :
    (L x).1 = (L (normalFacePoint (normalTangentialCoordinates x))).1 := by
  apply Subtype.ext
  rw [inwardChartSplit_tangent,inwardChartSplit_tangent,
    boundaryFoot_on_face _ (normalFacePoint_height _),boundaryFoot_apply]
  ext i
  by_cases hi : i = 0
  · subst i
    rw [normalFacePoint_height]
    simp [axis]
  · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
    simp [normalFacePoint,normalTangentialCoordinates,axis]

theorem inwardChartSplit_symm_height (q : Zt × ℝ) :
    ((inwardChartSplit (n := N)).symm q) 0 = q.2 := by
  rw [← inwardChartSplit_height,(inwardChartSplit (n := N)).apply_symm_apply]

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

omit [T2Space M] in
/-- The chart of an attached cap, in signed coordinates before the
push. Its metric field is exactly the one used in the metric gluing. -/
theorem AttachedCapSide.exists_signedInteriorChart
    {A : ProductBoundaryChart (n := N) (M := M) (Z := Zt)}
    {γ : MetricField N} {G : SmoothMetric N M} {cap : Set M} {embed : M → M}
    {b : Zt → ℝ} {e : (Zt × ℝ) ≃ (Zt × ℝ)}
    (C : AttachedCapSide A γ G cap embed b e)
    {V : Set E} (hV : IsOpen V) (hVA : V ⊆ L ⁻¹' A.ambient)
    (hVeq : ∀ x : E, e (L x) ∈ pushedCap b ↔ x ∈ V)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) :
    ∃ q : OpenPartialHomeomorph M E,
      q.source = cap ∧ q.target = V ∧
      (q : M → E) = (inwardChartSplit (n := N)).symm ∘ e.symm ∘ A.coord ∧
      (q.symm : E → M) = A.coord.symm ∘ e ∘ L ∧
      ContMDiffOn J K ∞ q q.source ∧ ContMDiffOn K J ∞ q.symm q.target ∧
      EqOn (coordinateMetric G q) C.field V := by
  have hEqCap : cap = A.coord.symm '' pushedCap b := by
    rw [C.cap_eq,C.shift.cap_eq,C.height_eq]
  let T := pushedCap b
  have hT : MapsTo (e ∘ L) V A.coord.target := by
    intro x hx
    have heW := (C.shift.coordinateShift_ambient (L x)).mpr (hVA hx)
    rw [C.push_eq] at heW
    have heP : e (L x) ∈ T := (hVeq x).mpr hx
    rw [A.target_eq]
    exact ⟨heW,mem_univ _,heP.1.le⟩
  have hTT : T ⊆ A.coord.target := by
    intro x hx
    have heq := (inwardChartSplit (n := N)).apply_symm_apply (e.symm x)
    have hv : (inwardChartSplit (n := N)).symm (e.symm x) ∈ V := by
      apply (hVeq _).mp
      rwa [heq,e.apply_symm_apply]
    have h := hT hv
    rwa [Function.comp_apply,heq,e.apply_symm_apply] at h
  have hSource : cap ⊆ A.coord.source := by
    rw [hEqCap]
    rintro _ ⟨x,hx,rfl⟩
    exact A.coord.map_target (hTT hx)
  have hPush : MapsTo A.coord cap T := by
    rw [hEqCap]
    rintro _ ⟨x,hx,rfl⟩
    rwa [A.coord.right_inv (hTT hx)]
  let f : M → E := (inwardChartSplit (n := N)).symm ∘ e.symm ∘ A.coord
  let fInv : E → M := A.coord.symm ∘ e ∘ L
  have hf : MapsTo f cap V := by
    intro x hx
    apply (hVeq _).mp
    change e (L ((inwardChartSplit (n := N)).symm (e.symm (A.coord x)))) ∈ T
    rw [(inwardChartSplit (n := N)).apply_symm_apply,e.apply_symm_apply]
    exact hPush hx
  have hfi : MapsTo fInv V cap := by
    intro x hx
    rw [hEqCap]
    exact mem_image_of_mem _ ((hVeq x).mpr hx)
  have hl (x : M) (hx : x ∈ cap) : fInv (f x) = x := by
    change A.coord.symm (e (L ((inwardChartSplit (n := N)).symm (e.symm (A.coord x))))) = x
    rw [(inwardChartSplit (n := N)).apply_symm_apply,e.apply_symm_apply,A.coord.left_inv (hSource hx)]
  have hr (x : E) (hx : x ∈ V) : f (fInv x) = x := by
    change (inwardChartSplit (n := N)).symm (e.symm (A.coord (A.coord.symm (e (L x))))) = x
    have hT' : e (L x) ∈ A.coord.target := hT hx
    rw [A.coord.right_inv hT',e.symm_apply_apply,(inwardChartSplit (n := N)).symm_apply_apply]
  have hF : ContMDiffOn J K ∞ f cap :=
    ((inwardChartSplit (n := N)).symm.contDiff.contMDiff.comp_contMDiffOn
      (hei.contMDiff.comp_contMDiffOn A.smooth)).mono hSource
  have hFi : ContMDiffOn K J ∞ fInv V :=
    A.smooth_inverse.comp (he.contMDiff.comp (inwardChartSplit (n := N)).contDiff.contMDiff).contMDiffOn hT
  let q : OpenPartialHomeomorph M E :=
    { toFun := f
      invFun := fInv
      source := cap
      target := V
      map_source' := hf
      map_target' := hfi
      left_inv' := hl
      right_inv' := hr
      continuousOn_toFun := hF.continuousOn
      continuousOn_invFun := hFi.continuousOn
      open_source := C.cap_eq.symm ▸ C.shift.open_cap
      open_target := hV }
  refine ⟨q,rfl,rfl,rfl,rfl,hF,hFi,?_⟩
  intro x hx
  let Df : TangentSpace J (fInv x) →L[ℝ] E := mfderiv J K f (fInv x)
  let Di : E →L[ℝ] TangentSpace J (fInv x) := mfderiv K J fInv x
  have hMD : q.MDifferentiable J K :=
    ⟨hF.mdifferentiableOn (by simp),hFi.mdifferentiableOn (by simp)⟩
  have hCLM : Df.comp Di = ContinuousLinearMap.id ℝ E := hMD.comp_symm_deriv hx
  have hAt (v : E) : Df (Di v) = v := DFunLike.congr_fun hCLM v
  ext i j
  change G.inner (fInv x) ((mfderiv K J fInv x) (axis i)) ((mfderiv K J fInv x) (axis j)) =
    C.field x i j
  rw [C.realizes _ (hSource (hfi hx)),nativeCoordinateBilinear_apply]
  change metricPair C.field (f (fInv x)) (Df (Di (axis i))) (Df (Di (axis j))) = _
  rw [hr x hx,hAt,hAt]
  simp [metricPair,axis]

end CalderonPatch
