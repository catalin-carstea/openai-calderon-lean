module

public import Proof.CalderonPatch.ConnectedInterior

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

@[expose] public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- Restrict the extended chart to any open Euclidean subset of its target. -/
theorem exists_interiorChart_restrict (p : M) {V : Set (X n)}
    (hV : IsOpen V) (hSub : V ⊆ (extChartAt J p).target) :
    ∃ e : OpenPartialHomeomorph M (X n),
      e.target = V ∧ e.source = (extChartAt J p).source ∩ (extChartAt J p) ⁻¹' V ∧
      (e : M → X n) = extChartAt J p ∧ (e.symm : X n → M) = (extChartAt J p).symm ∧
      e.source ⊆ (𝓡∂ n).interior M ∧ ContMDiffOn J K ∞ e e.source ∧
      ContMDiffOn K J ∞ e.symm e.target := by
  let c := extChartAt J p
  let S := c ⁻¹' V
  have hImage : c.IsImage S V := fun _ _ => Iff.rfl
  let R := hImage.symm.restr
  have hR : R.source = V := inter_eq_right.mpr hSub
  have hOpen : IsOpen R.source := hR.symm ▸ hV
  have hCont : ContinuousOn R R.source := (continuousOn_extChartAt_symm p).mono (fun _ hx => hx.1)
  have hMap : IsOpenMap (R.source.domRestrict R) := by
    intro U hU
    let U' : Set (X n) := Subtype.val '' U
    have hU' : IsOpen U' := hOpen.isOpenMap_subtype_val U hU
    have hU'sub : U' ⊆ c.target := by
      rintro _ ⟨x, hx, rfl⟩
      exact x.property.1
    have hEq : (fun x : R.source => c.symm x) '' U = c.symm '' U' := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    change IsOpen ((fun x : R.source => c.symm x) '' U)
    rw [hEq]
    rw [c.symm.image_eq_target_inter_inv_preimage hU'sub]
    exact (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) hU'
  let e := (OpenPartialHomeomorph.ofContinuousOpenRestrict R hCont hMap hOpen).symm
  refine ⟨e, hR, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro x hx
    have hxs : x ∈ (chartAt (EuclideanHalfSpace n) p).source := by
      simpa only [c, extChartAt_source] using (show x ∈ c.source from hx.1)
    apply ((𝓡∂ n).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas _ p) hxs).2
    exact interior_maximal hSub hV hx.2
  · exact (contMDiffOn_extChartAt (I := J) (x := p)).mono (fun _ hx =>
      by simpa only [c, extChartAt_source] using (show _ ∈ c.source from hx.1))
  · exact (contMDiffOn_extChartAt_symm (I := J) p).mono (fun _ hx => hx.1)

/-- Every interior point has a smooth open coordinate chart inside any
specified open neighborhood. -/
theorem exists_interiorChart (p : M) (hp : p ∈ (𝓡∂ n).interior M)
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ e : OpenPartialHomeomorph M (X n),
      p ∈ e.source ∧ e.source ⊆ U ∧ e.source ⊆ (𝓡∂ n).interior M ∧
      ContMDiffOn J K ∞ e e.source ∧ ContMDiffOn K J ∞ e.symm e.target := by
  let c := extChartAt J p
  let V := interior c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V :=
    ((continuousOn_extChartAt_symm p).mono interior_subset).isOpen_inter_preimage isOpen_interior hU
  obtain ⟨e, _, hs, _, _, hI, he, hinv⟩ :=
    exists_interiorChart_restrict p hV (fun _ hx => interior_subset hx.1)
  have hps : p ∈ c.source := mem_extChartAt_source p
  refine ⟨e, ?_, ?_, hI, he, hinv⟩
  · rw [hs]
    refine ⟨hps, (𝓡∂ n).isInteriorPoint_iff.mp hp, ?_⟩
    change c.symm (c p) ∈ U
    rwa [c.left_inv hps]
  · intro x hx
    rw [hs] at hx
    exact c.left_inv hx.1 ▸ hx.2.2

end CalderonPatch
