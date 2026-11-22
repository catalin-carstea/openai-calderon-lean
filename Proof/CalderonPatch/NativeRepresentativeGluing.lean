module

public import Proof.CalderonPatch.DirichletWeakGreen

import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.MeasureTheory.Measure.OpenPos

public section

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Manifold Topology

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)

/-- Smooth local representatives of a fixed native (L^2) value agree
on overlaps, including their boundary points. -/
theorem exists_smooth_zero_trace_ae_eq_of_locally
    (D : DirichletData m M) {U : Set M} (hU : IsOpen U) {v : M → ℝ}
    (h : ∀ x ∈ U, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ⊆ U ∧
      ∃ u : M → ℝ, ContMDiffOn J R ∞ u O ∧ EqOn u 0 (O ∩ (J).boundary M) ∧
        v =ᵐ[D.volume.restrict O] u) :
    ∃ u : M → ℝ, ContMDiffOn J R ∞ u U ∧ EqOn u 0 (U ∩ (J).boundary M) ∧
      v =ᵐ[D.volume.restrict U] u := by
  classical
  let : SecondCountableTopology (EuclideanHalfSpace (m+1)) := by
    unfold EuclideanHalfSpace
    infer_instance
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanHalfSpace (m+1)) M
  let : D.volume.IsOpenPosMeasure :=
    ⟨fun _ hO hOn => (D.metric_volume.measure_pos_of_open_nonempty hO hOn).ne'⟩
  choose O hO hxO hOU f hf hf0 hfv using fun x : U => h x x.property
  let u (x : M) := if hx : x ∈ U then f ⟨x,hx⟩ x else 0
  have hEq (a : U) : EqOn u (f a) (O a) := by
    intro x hx
    have hxU := hOU a hx
    let b : U := ⟨x,hxU⟩
    have hOverlap : IsOpen (O b ∩ O a) := (hO b).inter (hO a)
    have hA := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_right : O b ∩ O a ⊆ O a) (hfv a)
    have hB := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_left : O b ∩ O a ⊆ O b) (hfv b)
    have he := Measure.eqOn_open_of_ae_eq ((EventuallyEq.symm hB).trans hA) hOverlap
      ((hf b).continuousOn.mono inter_subset_left) ((hf a).continuousOn.mono inter_subset_right)
      (show x ∈ O b ∩ O a from ⟨hxO b,hx⟩)
    simpa only [u,dite_eq_left hxU] using he
  refine ⟨u,?_,?_,?_⟩
  · intro x hxU
    let a : U := ⟨x,hxU⟩
    exact (((hf a).contMDiffAt ((hO a).mem_nhds (hxO a))).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((hO a).mem_nhds (hxO a)) (hEq a))).contMDiffWithinAt
  · intro x hx
    let a : U := ⟨x,hx.1⟩
    rw [hEq a (hxO a)]
    exact hf0 a ⟨hxO a,hx.2⟩
  · rw [Filter.EventuallyEq,ae_restrict_iff' hU.measurableSet,ae_iff]
    apply measure_null_of_locally_null
    intro x hx
    have hxU : x ∈ U := by by_contra hn; exact hx (fun hh => (hn hh).elim)
    let a : U := ⟨x,hxU⟩
    refine ⟨_, inter_mem_nhdsWithin _ ((hO a).mem_nhds (hxO a)),?_⟩
    apply measure_mono_null _ (ae_iff.1 (ae_imp_of_ae_restrict (hfv a)))
    rintro y ⟨hy,hyO⟩ hEq'
    exact hy (fun _ => (hEq' hyO).trans (hEq a hyO).symm)

end CalderonPatch
