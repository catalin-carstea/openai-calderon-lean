module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Maps.Proper.Basic

public section

open Filter Set
open scoped Topology

namespace CalderonPatch

/-- The evaluation data used to identify points in the compact extensions. -/
structure SourceEvaluations (M F : Type*) [TopologicalSpace M] where
  interior : Set M
  value : M → F → ℝ
  continuous : Continuous value
  interior_ne_zero : ∀ p ∈ interior, value p ≠ 0
  zero_outside_interior : ∀ p ∉ interior, value p = 0
  separates : InjOn value interior

variable {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Equal evaluations, with the domain of the match as the first component. -/
def evaluationGraph (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F) : Set (X × Y) :=
  {p | I₂.value p.1 = I₁.value p.2}

theorem isClosed_evaluationGraph (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F) :
    IsClosed (evaluationGraph I₂ I₁) :=
  isClosed_eq (I₂.continuous.comp continuous_fst) (I₁.continuous.comp continuous_snd)

theorem interior_of_equal_evaluations (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    {p : X} {q : Y} (hp : p ∈ I₂.interior) (h : I₂.value p = I₁.value q) : q ∈ I₁.interior := by
  by_contra hq
  exact I₂.interior_ne_zero p hp (h.trans (I₁.zero_outside_interior q hq))

/-- Compactness produces a partner for every limit of matched points.
Interior nonvanishing and separation give uniqueness at the frontier. -/
theorem existsUnique_partner_of_mem_closure [CompactSpace Y]
    (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    {W : Set X} {p : X} (hp : p ∈ I₂.interior) (hcl : p ∈ closure W)
    (hW : ∀ x ∈ W, ∃ y, I₂.value x = I₁.value y) :
    ∃! q, I₂.value p = I₁.value q := by
  have hclosed : IsClosed (Prod.fst '' evaluationGraph I₂ I₁) :=
    isClosedMap_fst_of_compactSpace _ (isClosed_evaluationGraph I₂ I₁)
  have hsub : W ⊆ Prod.fst '' evaluationGraph I₂ I₁ := by
    intro x hx
    obtain ⟨y, hy⟩ := hW x hx
    exact ⟨(x, y), hy, rfl⟩
  obtain ⟨⟨x, q⟩, hq, rfl⟩ := closure_minimal hsub hclosed hcl
  have hqI := interior_of_equal_evaluations I₂ I₁ hp hq
  refine ⟨q, hq, fun y hy => I₁.separates (interior_of_equal_evaluations I₂ I₁ hp hy) hqI ?_⟩
  exact hy.symm.trans hq

/-- All partners of nearby points lie near the unique limiting partner.
This uses the one relation for all sources at once. -/
theorem eventually_partners_mem [CompactSpace Y]
    (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    {p : X} {q : Y} {V : Set Y} (hV : V ∈ 𝓝 q)
    (hq : ∀ y, I₂.value p = I₁.value y → y = q) :
    ∀ᶠ x in 𝓝 p, ∀ y, I₂.value x = I₁.value y → y ∈ V := by
  obtain ⟨U, hUV, hU, hqU⟩ := mem_nhds_iff.mp hV
  let bad : Set X := Prod.fst '' (evaluationGraph I₂ I₁ ∩ Prod.snd ⁻¹' Uᶜ)
  have hbad : IsClosed bad := isClosedMap_fst_of_compactSpace _
    ((isClosed_evaluationGraph I₂ I₁).inter (hU.isClosed_compl.preimage continuous_snd))
  have hp : p ∈ badᶜ := by
    rintro ⟨⟨x, y⟩, ⟨hxy, hy⟩, rfl⟩
    exact hy ((hq y hxy).symm ▸ hqU)
  filter_upwards [hbad.isOpen_compl.mem_nhds hp] with x hx y hxy
  apply hUV
  by_contra hy
  exact hx ⟨(x, y), ⟨hxy, hy⟩, rfl⟩

/-- The full interior matching relation has closed image in the target
interior, using compactness of the source extension. -/
theorem isClosed_targetInterior_range [CompactSpace X]
    (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F) :
    IsClosed {q : I₁.interior | ∃ p ∈ I₂.interior, I₂.value p = I₁.value q} := by
  have hclosed : IsClosed (Prod.snd '' evaluationGraph I₂ I₁) :=
    isClosedMap_snd_of_compactSpace _ (isClosed_evaluationGraph I₂ I₁)
  convert hclosed.preimage continuous_subtype_val using 1
  ext q
  change (∃ p ∈ I₂.interior, I₂.value p = I₁.value q) ↔
    (q : Y) ∈ Prod.snd '' evaluationGraph I₂ I₁
  constructor
  · rintro ⟨p, _, hpq⟩
    exact ⟨(p, q), hpq, rfl⟩
  · rintro ⟨⟨p, _⟩, hpq, rfl⟩
    exact ⟨p, interior_of_equal_evaluations I₁ I₂ q.property (Eq.symm hpq), hpq⟩

end CalderonPatch
