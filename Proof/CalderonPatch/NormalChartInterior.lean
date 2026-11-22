module

public import Proof.CalderonPatch.NativeBoundaryMetricChart
public import Proof.CalderonPatch.CoordinateMetric

public section

noncomputable section
open Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X axis metricPair)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "Pos" => positiveHalfSpace n

/-- On the positive side of a signed normal chart, the native
coordinate Laplacian uses its actual normal metric field. -/
theorem NativeBoundaryMetricChart.exists_interior_restriction
    {g : SmoothMetric n M} {p : M} (D : NativeBoundaryMetricChart g p)
    {U : Set (X n)} (hU : IsOpen U) (hUD : U ⊆ D.ambient) :
    ∃ e : OpenPartialHomeomorph M (X n), e.target = U ∩ Pos ∧
      (e : M → X n) = D.coord ∧ (e.symm : X n → M) = D.coord.symm ∧
      e.source ⊆ (J).interior M ∧
      ContMDiffOn J K ∞ e e.source ∧ ContMDiffOn K J ∞ e.symm e.target ∧
      EqOn (coordinateMetric g e) D.field e.target := by
  let T := U ∩ Pos
  let S := D.coord.source ∩ D.coord ⁻¹' T
  have hT : IsOpen T := hU.inter isOpen_positiveHalfSpace
  have hTD : T ⊆ D.coord.target := fun x hx =>
    D.target_eq.symm ▸ ⟨hUD hx.1,positiveHalfSpace_subset_inwardHalfSpace hx.2⟩
  have hS : IsOpen S := D.smooth.continuousOn.isOpen_inter_preimage D.open_source hT
  let e : OpenPartialHomeomorph M (X n) :=
    { toFun := D.coord
      invFun := D.coord.symm
      source := S
      target := T
      map_source' := fun _ hx => hx.2
      map_target' := fun x hx => ⟨D.coord.map_target (hTD hx), by
        change D.coord (D.coord.symm x) ∈ T
        rwa [D.coord.right_inv (hTD hx)]⟩
      left_inv' := fun _ hx => D.coord.left_inv hx.1
      right_inv' := fun _ hx => D.coord.right_inv (hTD hx)
      open_source := hS
      open_target := hT
      continuousOn_toFun := D.smooth.continuousOn.mono inter_subset_left
      continuousOn_invFun := D.smooth_inverse.continuousOn.mono hTD }
  have he : ContMDiffOn J K ∞ e e.source := D.smooth.mono inter_subset_left
  have hes : ContMDiffOn K J ∞ e.symm e.target := D.smooth_inverse.mono hTD
  refine ⟨e,rfl,rfl,rfl,(fun x hx => (D.interior_iff x hx.1).mpr hx.2.2),he,hes,?_⟩
  have hDiff : e.MDifferentiable J K :=
    ⟨he.mdifferentiableOn (by simp),hes.mdifferentiableOn (by simp)⟩
  intro x hx
  have hs := e.map_target hx
  have hComp := hDiff.comp_symm_deriv hx
  have hAx (v : X n) : mfderiv J K D.coord (D.coord.symm x)
      (mfderiv K J D.coord.symm x v) = v := DFunLike.congr_fun hComp v
  ext a b
  change g.inner (D.coord.symm x) (mfderiv K J D.coord.symm x (axis a))
    (mfderiv K J D.coord.symm x (axis b)) = D.field x a b
  have hsD : D.coord.symm x ∈ D.coord.source := hs.1
  rw [D.realizes _ hsD, hAx, hAx, D.coord.right_inv (hTD hx)]
  simp [metricPair,axis]

end CalderonPatch
