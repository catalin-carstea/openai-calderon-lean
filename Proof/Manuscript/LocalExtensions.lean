module

public import Proof.Manuscript.Lemma81Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue

public section

open Set Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Set E} {f : E → V}

theorem SmoothThrough.continuousOn (hf : SmoothThrough (closure Ω) f) :
    ContinuousOn f (closure Ω) := by
  intro x hx
  obtain ⟨U, hU, hxU, g, hg, heq⟩ := hf x hx
  have hevent : f =ᶠ[𝓝[closure Ω] x] g := Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨U ∩ closure Ω,
      inter_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)) self_mem_nhdsWithin,
      heq.symm⟩
  exact ((hg.continuousOn.continuousAt (hU.mem_nhds hxU)).continuousWithinAt)
    |>.congr_of_eventuallyEq_of_mem hevent hx

theorem SmoothThrough.contDiffOn_interior (hf : SmoothThrough (closure Ω) f) (hΩ : IsOpen Ω) :
    ContDiffOn ℝ ∞ f Ω := by
  intro x hx
  obtain ⟨U, hU, hxU, g, hg, heq⟩ := hf x (subset_closure hx)
  have hEq : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨U ∩ Ω, (hU.inter hΩ).mem_nhds ⟨hxU, hx⟩,
      fun y hy => (heq ⟨hy.1, subset_closure hy.2⟩).symm⟩
  exact ((hg.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq hEq).contDiffWithinAt

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem eqOn_closure_of_continuousOn {Ω : Set E} {f g : E → V}
    (hf : ContinuousOn f (closure Ω)) (hg : ContinuousOn g (closure Ω))
    (heq : EqOn f g Ω) : EqOn f g (closure Ω) := by
  intro x hx
  have := mem_closure_iff_nhdsWithin_neBot.mp hx
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hf x hx).mono subset_closure) ((hg x hx).mono subset_closure)
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, self_mem_nhdsWithin, heq⟩)

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem eq_at_closure_of_eqOn_local {U Ω : Set E} {p : E} {f g : E → V}
    (hU : IsOpen U) (hp : p ∈ U) (hpΩ : p ∈ closure Ω)
    (hf : ContinuousAt f p) (hg : ContinuousAt g p) (heq : EqOn f g (U ∩ Ω)) :
    f p = g p := by
  have hcl := hU.inter_closure ⟨hp, hpΩ⟩
  have := mem_closure_iff_nhdsWithin_neBot.mp hcl
  exact tendsto_nhds_unique_of_eventuallyEq
    hf.continuousWithinAt hg.continuousWithinAt
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U ∩ Ω, self_mem_nhdsWithin, heq⟩)

omit [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem SmoothThrough.eventuallyEq_extension {U : Set E} {g : E → V} {x : E}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hx : x ∈ U ∩ Ω)
    (heq : EqOn g f (U ∩ closure Ω)) : g =ᶠ[𝓝 x] f := by
  filter_upwards [(hU.inter hΩ).mem_nhds hx] with y hy
  exact heq ⟨hy.1, subset_closure hy.2⟩

end CalderonPaper
