module

public import Proof.CalderonN.Coordinates
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen

public section

open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

/-- A dense subset is preconnected if its intersections with suitable
neighborhoods of every point of the ambient connected set are preconnected. -/
theorem isPreconnected_of_dense_local_intersections
    {M : Type*} [TopologicalSpace M] {U S : Set M} (hU : IsPreconnected U)
    (hSU : S ⊆ U) (hDense : U ⊆ closure S)
    (hlocal : ∀ p ∈ U, ∃ V ∈ 𝓝 p, IsPreconnected (V ∩ S)) : IsPreconnected S := by
  refine isPreconnected_iff_subset_of_disjoint.mpr fun A B hA hB hAB hdis => ?_
  let O₁ := (closure (S ∩ B))ᶜ
  let O₂ := (closure (S ∩ A))ᶜ
  have hcover : U ⊆ O₁ ∪ O₂ := by
    intro p hp
    obtain ⟨V, hV, hConn⟩ := hlocal p hp
    have hVAB : V ∩ S ⊆ A ∪ B := inter_subset_right.trans hAB
    have hVdis : (V ∩ S) ∩ (A ∩ B) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh : x ∈ S ∩ (A ∩ B) := ⟨hx.1.2, hx.2⟩
      rwa [hdis] at hh
    rcases (isPreconnected_iff_subset_of_disjoint.mp hConn) A B hA hB hVAB hVdis with h | h
    · left
      intro hc
      obtain ⟨x, hxV, hxS, hxB⟩ := mem_closure_iff_nhds.mp hc V hV
      have hh : x ∈ S ∩ (A ∩ B) := ⟨hxS, h ⟨hxV, hxS⟩, hxB⟩
      rwa [hdis] at hh
    · right
      intro hc
      obtain ⟨x, hxV, hxS, hxA⟩ := mem_closure_iff_nhds.mp hc V hV
      have hh : x ∈ S ∩ (A ∩ B) := ⟨hxS, hxA, h ⟨hxV, hxS⟩⟩
      rwa [hdis] at hh
  have hDisjO : U ∩ (O₁ ∩ O₂) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hsub : S ⊆ (S ∩ A) ∪ (S ∩ B) := by
      intro y hy
      rcases hAB hy with hA | hB
      · exact Or.inl ⟨hy, hA⟩
      · exact Or.inr ⟨hy, hB⟩
    have hc := closure_mono hsub (hDense hx.1)
    rw [closure_union] at hc
    exact hc.elim hx.2.2 hx.2.1
  rcases (isPreconnected_iff_subset_of_disjoint.mp hU) O₁ O₂
    isClosed_closure.isOpen_compl isClosed_closure.isOpen_compl hcover hDisjO with h | h
  · left
    intro x hx
    rcases hAB hx with hA | hxB
    · exact hA
    · exact False.elim ((h (hSU hx)) (subset_closure ⟨hx, hxB⟩))
  · right
    intro x hx
    rcases hAB hx with hxA | hB
    · exact False.elim ((h (hSU hx)) (subset_closure ⟨hx, hxA⟩))
    · exact hB

section ManifoldInterior

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n

private theorem mem_manifoldInterior_of_mem_extChartAt_interior (p : M) {x : X n}
    (hx : x ∈ interior (extChartAt J p).target) : (extChartAt J p).symm x ∈ (𝓡∂ n).interior M := by
  let e := extChartAt J p
  have hy := e.map_target (interior_subset hx)
  have hy' : e.symm x ∈ (chartAt (EuclideanHalfSpace n) p).source := by
    simpa only [e, extChartAt_source] using hy
  apply ((𝓡∂ n).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas _ p) hy').2
  change e (e.symm x) ∈ interior e.target
  rwa [e.right_inv (interior_subset hx)]

theorem dense_manifoldInterior : Dense ((𝓡∂ n).interior M) := by
  intro p
  let e := extChartAt J p
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hc : e p ∈ closure (interior e.target) :=
    extChartAt_target_subset_closure_interior (e.map_source hp)
  have hcl := mem_closure_image (continuousAt_extChartAt_symm (I := J) p) hc
  have hsub : e.symm '' interior e.target ⊆ (𝓡∂ n).interior M := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_manifoldInterior_of_mem_extChartAt_interior p hx
  exact e.left_inv hp ▸ closure_mono hsub hcl

/-- The interior of a connected half-space manifold is connected.
Each sufficiently small extended-chart ball meets the interior in
the inverse image of a convex open half-ball. -/
theorem isConnected_manifoldInterior [ConnectedSpace M] :
    IsConnected ((𝓡∂ n).interior M) := by
  let S := (𝓡∂ n).interior M
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  obtain ⟨x, hx⟩ := interior_extChartAt_target_nonempty J p
  refine ⟨⟨_, mem_manifoldInterior_of_mem_extChartAt_interior p hx⟩, ?_⟩
  apply isPreconnected_of_dense_local_intersections isPreconnected_univ (subset_univ S)
    (fun p _ => dense_manifoldInterior p)
  intro p _
  let e := extChartAt J p
  have hp : p ∈ e.source := mem_extChartAt_source p
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhdsWithin_iff.mp (extChartAt_target_mem_nhdsWithin (I := J) p)
  let B := ball (e p) r
  let V := e.source ∩ e ⁻¹' B
  have hV : V ∈ 𝓝 p :=
    inter_mem ((isOpen_extChartAt_source p).mem_nhds hp)
      ((continuousAt_extChartAt p).preimage_mem_nhds (ball_mem_nhds _ hr))
  refine ⟨V, hV, ?_⟩
  have hTarget : B ∩ interior e.target = B ∩ interior (range J) := by
    refine Subset.antisymm
      (inter_subset_inter_right _ (interior_mono (extChartAt_target_subset_range (I := J) p))) ?_
    rintro y ⟨hyB, hyI⟩
    have hi : y ∈ interior (B ∩ range J) := by
      rw [interior_inter, isOpen_ball.interior_eq]
      exact ⟨hyB, hyI⟩
    exact ⟨hyB, interior_mono hB hi⟩
  have hImage : V ∩ S = e.symm '' (B ∩ interior e.target) := by
    ext y
    constructor
    · rintro ⟨⟨hy, hyB⟩, hyI⟩
      have hy' : y ∈ (chartAt (EuclideanHalfSpace n) p).source := by
        simpa only [e, extChartAt_source] using hy
      have hi := ((𝓡∂ n).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
        (chart_mem_atlas _ p) hy').1 hyI
      exact ⟨e y, ⟨hyB, hi⟩, e.left_inv hy⟩
    · rintro ⟨z, ⟨hzB, hzI⟩, rfl⟩
      have hzt := interior_subset hzI
      exact ⟨⟨e.map_target hzt, by simpa only [mem_preimage, e.right_inv hzt] using hzB⟩,
        mem_manifoldInterior_of_mem_extChartAt_interior p hzI⟩
  rw [hImage]
  have hConvex : Convex ℝ (B ∩ interior (range J)) :=
    (convex_ball _ _).inter (𝓡∂ n).convex_range.interior
  rw [← hTarget] at hConvex
  exact hConvex.isPreconnected.image e.symm
    ((continuousOn_extChartAt_symm p).mono fun _ h => interior_subset h.2)

end ManifoldInterior

end CalderonPatch
