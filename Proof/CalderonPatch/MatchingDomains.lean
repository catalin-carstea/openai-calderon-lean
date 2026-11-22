module

public import Proof.CalderonPatch.EvaluationFrontier
public import Mathlib.Topology.IsLocalHomeomorph

import Mathlib.Topology.Connected.Clopen

public section

open Filter Set
open scoped Topology

namespace CalderonPatch

variable {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open partial identification respecting all source evaluations.
The caller supplies the extra local condition, such as smooth isometry. -/
structure EvaluationMatch (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    (admissible : OpenPartialHomeomorph X Y → Prop) where
  chart : OpenPartialHomeomorph X Y
  source_interior : chart.source ⊆ I₂.interior
  target_interior : chart.target ⊆ I₁.interior
  evaluation_eq : ∀ p ∈ chart.source, I₂.value p = I₁.value (chart p)
  property : admissible chart

/-- The union of all available open matching domains. -/
def matchingDomain (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    (admissible : OpenPartialHomeomorph X Y → Prop) : Set X :=
  ⋃ E : EvaluationMatch I₂ I₁ admissible, E.chart.source

theorem mem_matchingDomain
    {I₂ : SourceEvaluations X F} {I₁ : SourceEvaluations Y F}
    {admissible : OpenPartialHomeomorph X Y → Prop} {p : X} :
    p ∈ matchingDomain I₂ I₁ admissible ↔
      ∃ E : EvaluationMatch I₂ I₁ admissible, p ∈ E.chart.source :=
  mem_iUnion

theorem EvaluationMatch.source_subset_matchingDomain
    {I₂ : SourceEvaluations X F} {I₁ : SourceEvaluations Y F}
    {admissible : OpenPartialHomeomorph X Y → Prop} (E : EvaluationMatch I₂ I₁ admissible) :
    E.chart.source ⊆ matchingDomain I₂ I₁ admissible :=
  fun _ hp => mem_iUnion.mpr ⟨E, hp⟩

theorem matchingDomain_isOpen (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    (admissible : OpenPartialHomeomorph X Y → Prop) :
    IsOpen (matchingDomain I₂ I₁ admissible) :=
  isOpen_iUnion fun E => E.chart.open_source

theorem matchingDomain_subset_interior (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    (admissible : OpenPartialHomeomorph X Y → Prop) :
    matchingDomain I₂ I₁ admissible ⊆ I₂.interior := by
  intro p hp
  obtain ⟨E, hE⟩ := mem_iUnion.mp hp
  exact E.source_interior hE

/-- Evaluation separation makes the local identifications agree at every
common source point and gives an injective local homeomorphism on their union. -/
theorem exists_evaluationMatchGlue (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    (admissible : OpenPartialHomeomorph X Y → Prop) (defaultTarget : Y) :
    let W := matchingDomain I₂ I₁ admissible
    ∃ Φ : X → Y,
      IsLocalHomeomorphOn Φ W ∧ MapsTo Φ W I₁.interior ∧ InjOn Φ W ∧
      (∀ p ∈ W, I₂.value p = I₁.value (Φ p)) ∧
      ∀ E : EvaluationMatch I₂ I₁ admissible, EqOn Φ E.chart E.chart.source := by
  classical
  let W := matchingDomain I₂ I₁ admissible
  let chosen (p : X) (hp : p ∈ W) := (mem_iUnion.mp hp).choose
  have hchosen (p : X) (hp : p ∈ W) : p ∈ (chosen p hp).chart.source :=
    (mem_iUnion.mp hp).choose_spec
  let Φ (p : X) : Y := if hp : p ∈ W then (chosen p hp).chart p else defaultTarget
  have hΦ (p : X) (hp : p ∈ W) : Φ p = (chosen p hp).chart p := dif_pos hp
  have hMaps : MapsTo Φ W I₁.interior := by
    intro p hp
    rw [hΦ p hp]
    let E := chosen p hp
    exact E.target_interior (E.chart.map_source (hchosen p hp))
  have hEval (p : X) (hp : p ∈ W) : I₂.value p = I₁.value (Φ p) := by
    rw [hΦ p hp]
    exact (chosen p hp).evaluation_eq p (hchosen p hp)
  have hAgree (E : EvaluationMatch I₂ I₁ admissible) : EqOn Φ E.chart E.chart.source := by
    intro p hp
    have hpW : p ∈ W := mem_iUnion.mpr ⟨E, hp⟩
    exact I₁.separates (hMaps hpW) (E.target_interior (E.chart.map_source hp))
      ((hEval p hpW).symm.trans (E.evaluation_eq p hp))
  refine ⟨Φ, IsLocalHomeomorphOn.mk Φ W ?_, hMaps, ?_, hEval, hAgree⟩
  · intro p hp
    let E := chosen p hp
    exact ⟨E.chart, hchosen p hp, hAgree E⟩
  · intro p hp q hq hpq
    apply I₂.separates (matchingDomain_subset_interior I₂ I₁ admissible hp)
      (matchingDomain_subset_interior I₂ I₁ admissible hq)
    exact (hEval p hp).trans ((congrArg I₁.value hpq).trans (hEval q hq).symm)

/-- A match on the whole connected source interior is onto the connected
target interior. Compactness and the nonzero evaluations rule out a boundary
preimage of a limit of interior images. -/
theorem surjOn_interior_of_evaluationMatch [CompactSpace X]
    (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F) {Φ : X → Y}
    (hsource : IsOpen I₂.interior) (hne : I₂.interior.Nonempty)
    (hconn : IsConnected I₁.interior)
    (hLocal : IsLocalHomeomorphOn Φ I₂.interior) (hMaps : MapsTo Φ I₂.interior I₁.interior)
    (hEval : ∀ p ∈ I₂.interior, I₂.value p = I₁.value (Φ p)) :
    SurjOn Φ I₂.interior I₁.interior := by
  have hOpenImage : IsOpen (Φ '' I₂.interior) := by
    apply isOpen_iff_mem_nhds.2
    rintro _ ⟨p, hp, rfl⟩
    rw [← hLocal.map_nhds_eq hp]
    exact image_mem_map (hsource.mem_nhds hp)
  let A : Set I₁.interior := {q | ∃ p ∈ I₂.interior, I₂.value p = I₁.value q}
  have hImage : A = Subtype.val ⁻¹' (Φ '' I₂.interior) := by
    ext q
    constructor
    · rintro ⟨p, hp, hq⟩
      exact ⟨p, hp, I₁.separates (hMaps hp) q.property ((hEval p hp).symm.trans hq)⟩
    · rintro ⟨p, hp, hpq⟩
      exact ⟨p, hp, hpq ▸ hEval p hp⟩
  obtain ⟨p, hp⟩ := hne
  have hA : A.Nonempty := ⟨⟨Φ p, hMaps hp⟩, p, hp, hEval p hp⟩
  letI : ConnectedSpace I₁.interior := isConnected_iff_connectedSpace.mp hconn
  have hclopen : IsClopen A := ⟨isClosed_targetInterior_range I₂ I₁,
    hImage ▸ hOpenImage.preimage continuous_subtype_val⟩
  intro q hq
  have hqA : (⟨q, hq⟩ : I₁.interior) ∈ A := by rw [hclopen.eq_univ hA]; trivial
  rw [hImage] at hqA
  exact hqA

end CalderonPatch
