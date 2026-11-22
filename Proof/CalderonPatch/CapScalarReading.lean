module

public import Proof.CalderonPatch.SignedCapCoordinates
public import Proof.CalderonPatch.NormalChartFunctions

import Mathlib.Tactic

public section
noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "N" => (n+1)
local notation "E" => X N
local notation "Zt" => boundaryTangentPlane (0 : I N)
local notation "L" => (inwardChartSplit (n := N))
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

variable {A : ProductBoundaryChart (n := n+1) (M := M) (Z := boundaryTangentPlane (0 : I (n+1)))}
  {γ : MetricField (n+1)} {G : SmoothMetric (n+1) M} {cap : Set M} {embed : M → M}
  {b : boundaryTangentPlane (0 : I (n+1)) → ℝ}
  {e : (boundaryTangentPlane (0 : I (n+1)) × ℝ) ≃ (boundaryTangentPlane (0 : I (n+1)) × ℝ)}

omit [T2Space M] in
theorem AttachedCapSide.push_mem_target (S : AttachedCapSide A γ G cap embed b e)
    {x : E} (hx : x ∈ L ⁻¹' A.ambient) (ht : 0 ≤ (e (L x)).2) :
    e (L x) ∈ A.coord.target := by
  have he := (S.shift.coordinateShift_ambient (L x)).mpr hx
  rw [S.push_eq] at he
  rw [A.target_eq]
  exact ⟨he,mem_univ _,ht⟩

omit [T2Space M] in
/-- A smooth scalar on the extension has a genuinely signed smooth
representative before the push. On the pushed half space this is the
actual chart reading, including at the new boundary. -/
theorem AttachedCapSide.exists_signed_scalar_reading
    (S : AttachedCapSide A γ G cap embed b e) (he : ContDiff ℝ ∞ e)
    {w : M → ℝ} (hw : ContMDiff J R ∞ w)
    {K : Set E} (hK : IsCompact K) (hKA : K ⊆ L ⁻¹' A.ambient) :
    ∃ (r : E → ℝ) (V : Set E), ContDiff ℝ ∞ r ∧ IsOpen V ∧ K ⊆ V ∧
      V ⊆ L ⁻¹' A.ambient ∧
      EqOn r (w ∘ A.coord.symm ∘ e ∘ L) (V ∩ {x | 0 ≤ (e (L x)).2}) := by
  let f : E → Zt × ℝ := e ∘ L
  have hf : ContDiff ℝ ∞ f := he.comp (inwardChartSplit (n := N)).contDiff
  have hImage : f '' K ⊆ A.ambient := by
    rintro _ ⟨x,hx,rfl⟩
    have h := (S.shift.coordinateShift_ambient (L x)).mpr (hKA hx)
    rwa [S.push_eq] at h
  obtain ⟨v,U,hv,hU,hKU,hUA,hRead⟩ :=
    A.exists_smooth_function_extension hw (hK.image hf.continuous) hImage
  refine ⟨v ∘ f,f ⁻¹' U,hv.comp hf,hU.preimage hf.continuous,
    (fun x hx => hKU (mem_image_of_mem _ hx)),?_,?_⟩
  · intro x hx
    have h := hUA hx
    change e (L x) ∈ A.ambient at h
    rw [← S.push_eq] at h
    exact (S.shift.coordinateShift_ambient (L x)).mp h
  · intro x hx
    exact hRead ⟨hx.1,mem_univ _,hx.2⟩

omit [T2Space M] in
/-- In the positive signed collar the pushed scalar restricts to
the pullback along the original isometric embedding. -/
theorem AttachedCapSide.original_scalar_eq
    (S : AttachedCapSide A γ G cap embed b e)
    {w : M → ℝ} {x : E} (hx : x ∈ L ⁻¹' A.ambient) (hxH : x ∈ H) :
    w (embed (A.coord.symm (L x))) = w (A.coord.symm (e (L x))) := by
  have hxT : L x ∈ A.coord.target := by
    rw [A.target_eq]
    refine ⟨hx,mem_univ _,?_⟩
    rw [mem_Ici,inwardChartSplit_height]
    exact hxH
  have hxS := A.coord.map_target hxT
  have h := S.shift.coordinateShift_spec _ hxS
  rw [S.push_eq,A.coord.right_inv hxT] at h
  rw [S.embed_eq,← h.2,A.coord.left_inv h.1]

omit [T2Space M] in
/-- At the true pushed boundary, the signed scalar is zero. -/
theorem AttachedCapSide.scalar_zero_on_graph
    (S : AttachedCapSide A γ G cap embed b e) {w : M → ℝ}
    (hw : EqOn w 0 ((J).boundary M)) {x : E}
    (hx : x ∈ L ⁻¹' A.ambient) (ht : (e (L x)).2 = 0) :
    w (A.coord.symm (e (L x))) = 0 := by
  have hxT := S.push_mem_target hx ht.ge
  have hxS := A.coord.map_target hxT
  have hB : A.coord.symm (e (L x)) ∈ (J).boundary M := by
    rw [← (J).compl_interior]
    intro hI
    have hgt := (A.interior_iff _ hxS).mp hI
    rw [A.coord.right_inv hxT,ht] at hgt
    exact (lt_irrefl _ hgt)
  exact hw hB

omit [T2Space M] in
/-- Inverse coordinates for the normal chart and its product reading
coincide on the restricted collar. -/
theorem nativeInverse_eq_productInverse {D : ProductBoundaryChart (n := N) (M := M) (Z := Zt)}
    {g : SmoothMetric N M} {p : M} (A' : NativeBoundaryMetricChart g p)
    (hSource : A'.coord.source = D.coord.source)
    (hCoord : (A'.coord : M → E) = (inwardChartSplit (n := N)).symm ∘ D.coord)
    {W : Set (Zt × ℝ)} (hW : IsOpen W) (hWD : W ⊆ D.ambient) {x : E}
    (hx : x ∈ L ⁻¹' W ∩ H) :
    A'.coord.symm x = (D.restrictAmbient hW hWD).coord.symm (L x) := by
  let A := D.restrictAmbient hW hWD
  have hL : L x ∈ A.coord.target := by
    rw [A.target_eq]
    refine ⟨hx.1,mem_univ _,?_⟩
    rw [mem_Ici,inwardChartSplit_height]
    exact hx.2
  have hSource' : A.coord.symm (L x) ∈ A'.coord.source :=
    hSource.symm ▸ (A.coord.map_target hL).1
  have hc : A'.coord (A.coord.symm (L x)) = x := by
    rw [hCoord]
    change (inwardChartSplit (n := N)).symm (A.coord (A.coord.symm (L x))) = x
    rw [A.coord.right_inv hL,(inwardChartSplit (n := N)).symm_apply_apply]
  exact (congrArg A'.coord.symm hc.symm).trans (A'.coord.left_inv hSource')

omit [T2Space M] in
/-- A boundary value outside the touching region of a cap is still
zero after restricting a zero-boundary function to the original. -/
theorem AttachedCapSide.original_boundary_zero_of_not_touching
    (S : AttachedCapSide A γ G cap embed b e) (he : ∀ z, e (z,0) = (z,b z))
    {w : M → ℝ} (hw : EqOn w 0 ((J).boundary M))
    {p : M} (hp : p ∈ (J).boundary M) (hN : ¬ (p ∈ A.coord.source ∧ b (A.coord p).1 ≠ 0)) :
    w (embed p) = 0 := by
  rw [S.embed_eq]
  by_cases hpA : p ∈ A.coord.source
  · have hb : b (A.coord p).1 = 0 := not_not.mp (fun h => hN ⟨hpA,h⟩)
    have hp0 := A.height_eq_zero_on_boundary hp hpA
    have heq : e (A.coord p) = A.coord p := by
      have hc : A.coord p = ((A.coord p).1,0) := Prod.ext rfl hp0
      calc
        _ = e ((A.coord p).1,0) := congrArg e hc
        _ = ((A.coord p).1,0) := by rw [he,hb]
        _ = _ := hc.symm
    obtain ⟨hS,hEq⟩ := S.shift.coordinateShift_spec p hpA
    rw [S.push_eq,heq] at hEq
    have hEmb := A.coord.injOn hS hpA hEq
    rw [hEmb]
    exact hw hp
  · have hOut : p ∉ S.shift.support := fun h => hpA (S.shift.support_in_chart h)
    rw [S.shift.embed_eq_id_off_support hOut,id_eq]
    exact hw hp

end CalderonPatch
