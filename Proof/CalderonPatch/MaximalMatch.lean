module

public import Proof.CalderonPatch.MatchingDomains
public import Mathlib.Topology.Connected.LocallyConnected

import Mathlib.Topology.Connected.Clopen

public section

open Filter Set
open scoped Topology

namespace CalderonPatch

variable {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LocallyConnectedSpace X]

/-- An open connected matching chart that meets the seed component lies
wholly in that component. A chart with a point beyond the component thus
excludes an interior frontier, provided one is obtained at every contact. -/
theorem seedMatchingComponent_eq_interior
    (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    (admissible : OpenPartialHomeomorph X Y → Prop)
    (hInterior : IsConnected I₂.interior)
    {seed : X} (hseed : seed ∈ matchingDomain I₂ I₁ admissible)
    (hExtend :
      let W := connectedComponentIn (matchingDomain I₂ I₁ admissible) seed
      ∀ p ∈ I₂.interior, p ∈ closure W → p ∉ W →
        ∃ E : EvaluationMatch I₂ I₁ admissible,
          IsPreconnected E.chart.source ∧ (E.chart.source ∩ W).Nonempty ∧
          ∃ q ∈ E.chart.source, q ∉ W) :
    connectedComponentIn (matchingDomain I₂ I₁ admissible) seed = I₂.interior := by
  let D := matchingDomain I₂ I₁ admissible
  let W := connectedComponentIn D seed
  have hW : IsOpen W := (matchingDomain_isOpen I₂ I₁ admissible).connectedComponentIn
  have hseedW : seed ∈ W := mem_connectedComponentIn hseed
  have hWsub : W ⊆ I₂.interior :=
    (connectedComponentIn_subset D seed).trans (matchingDomain_subset_interior I₂ I₁ admissible)
  have hcl : I₂.interior ∩ closure W ⊆ W := by
    intro p hp
    by_contra hout
    obtain ⟨E, hconn, ⟨x, hx, hxW⟩, y, hy, hyW⟩ := hExtend p hp.1 hp.2 hout
    have hE : E.chart.source ⊆ D := E.source_subset_matchingDomain
    have hy' : y ∈ connectedComponentIn D x := hconn.subset_connectedComponentIn hx hE hy
    exact hyW ((connectedComponentIn_eq hxW).symm ▸ hy')
  have hcover : I₂.interior ⊆ W ∪ (closure W)ᶜ := fun _ hp =>
    or_iff_not_imp_right.mpr fun h => hcl ⟨hp, not_not.mp h⟩
  have hdis : I₂.interior ∩ (W ∩ (closure W)ᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.2.2 (subset_closure hx.2.1)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hInterior.2) W (closure W)ᶜ
    hW isClosed_closure.isOpen_compl hcover hdis with h | h
  · exact Subset.antisymm hWsub h
  · exact False.elim ((h (hWsub hseedW)) (subset_closure hseedW))

/-- Glue a maximal match to a homeomorphism of the interiors once the
matching charts exclude a frontier. It agrees with every local match. -/
theorem exists_interiorEvaluationHomeomorph [CompactSpace X]
    (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    (admissible : OpenPartialHomeomorph X Y → Prop)
    (hSourceOpen : IsOpen I₂.interior) (hSource : IsConnected I₂.interior)
    (hTarget : IsConnected I₁.interior)
    {seed : X} (hseed : seed ∈ matchingDomain I₂ I₁ admissible)
    (hExtend :
      let W := connectedComponentIn (matchingDomain I₂ I₁ admissible) seed
      ∀ p ∈ I₂.interior, p ∈ closure W → p ∉ W →
        ∃ E : EvaluationMatch I₂ I₁ admissible,
          IsPreconnected E.chart.source ∧ (E.chart.source ∩ W).Nonempty ∧
          ∃ q ∈ E.chart.source, q ∉ W) :
    ∃ e : OpenPartialHomeomorph X Y, e.source = I₂.interior ∧ e.target = I₁.interior ∧
      (∀ p ∈ e.source, I₂.value p = I₁.value (e p)) ∧
      (∀ p ∈ e.source, ∃ E : EvaluationMatch I₂ I₁ admissible, p ∈ E.chart.source) ∧
      ∀ E : EvaluationMatch I₂ I₁ admissible, EqOn e E.chart E.chart.source := by
  let D := matchingDomain I₂ I₁ admissible
  have hDomain : D = I₂.interior := by
    refine Subset.antisymm (matchingDomain_subset_interior I₂ I₁ admissible) ?_
    rw [← seedMatchingComponent_eq_interior I₂ I₁ admissible hSource hseed hExtend]
    exact connectedComponentIn_subset D seed
  obtain ⟨E₀, _⟩ := mem_matchingDomain.mp hseed
  obtain ⟨Φ, hLocal, hMaps, hInj, hEval, hAgree⟩ :=
    exists_evaluationMatchGlue I₂ I₁ admissible (E₀.chart seed)
  change IsLocalHomeomorphOn Φ D at hLocal
  change MapsTo Φ D I₁.interior at hMaps
  change InjOn Φ D at hInj
  change (∀ p ∈ D, I₂.value p = I₁.value (Φ p)) at hEval
  rw [hDomain] at hLocal hMaps hInj hEval
  have hSurj := surjOn_interior_of_evaluationMatch I₂ I₁ hSourceOpen hSource.1 hTarget hLocal hMaps hEval
  let _ : Nonempty X := ⟨seed⟩
  let pe := BijOn.toPartialEquiv Φ I₂.interior I₁.interior ⟨hMaps, hInj, hSurj⟩
  have hOpen : IsOpenMap (I₂.interior.domRestrict Φ) := by
    intro U hU
    have hU' := hSourceOpen.isOpenMap_subtype_val U hU
    apply isOpen_iff_mem_nhds.2
    rintro _ ⟨p, hp, rfl⟩
    change (I₂.interior.domRestrict Φ) '' U ∈ 𝓝 (Φ p)
    rw [← hLocal.map_nhds_eq p.property]
    have hImg : Φ '' (Subtype.val '' U) ∈ map Φ (𝓝 (p : X)) :=
      image_mem_map (hU'.mem_nhds ⟨p, hp, rfl⟩)
    change (fun x : I₂.interior => Φ x) '' U ∈ map Φ (𝓝 (p : X))
    simpa only [image_image] using hImg
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe hLocal.continuousOn hOpen hSourceOpen
  refine ⟨e, rfl, rfl, hEval, ?_, hAgree⟩
  intro p hp
  have hp' : p ∈ I₂.interior := hp
  exact mem_matchingDomain.mp (show p ∈ D from hDomain.symm ▸ hp')

end CalderonPatch
