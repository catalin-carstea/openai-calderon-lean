module

public import Proof.CalderonPatch.InteriorChartBasis
public import Proof.CalderonN.ChartUniqueContinuation

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen

public section

open Filter Metric Set
open scoped Topology

namespace CalderonPatch

open CalderonN (X MetricField Harmonic)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]

/-- Scalar unique continuation on a connected open manifold region follows
from the checked coordinate unique-continuation theorem. The same local
metric must make both functions harmonic. -/
theorem eqOn_of_locally_harmonic {U V : Set M} {u v : M → ℝ}
    (hU : IsOpen U) (hConn : IsConnected U) (hV : IsOpen V) (hVne : V.Nonempty)
    (hVU : V ⊆ U) (hEq : EqOn u v V)
    (hLocal : ∀ p ∈ U, ∃ e : OpenPartialHomeomorph M (X n),
      p ∈ e.source ∧ e.source ⊆ U ∧ ∃ γ : MetricField n,
      CalderonN.SmoothMetric e.target γ ∧ Harmonic e.target γ (u ∘ e.symm) ∧
        Harmonic e.target γ (v ∘ e.symm)) : EqOn u v U := by
  let E := interior (U ∩ {p | u p = v p})
  have hE : IsOpen E := isOpen_interior
  have hEU : E ⊆ U := interior_subset.trans inter_subset_left
  have hVE : V ⊆ E := interior_maximal (fun x hx => ⟨hVU hx, hEq hx⟩) hV
  have hclosed : U ∩ closure E ⊆ E := by
    intro p hp
    obtain ⟨e, hpE, heU, γ, hγ, hu, hv⟩ := hLocal p hp.1
    obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hpE))
    let B := ball (e p) r
    let O := e.source ∩ e ⁻¹' B
    have hO : IsOpen O := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
    have hpO : p ∈ O := ⟨hpE, mem_ball_self hr⟩
    have hMeet : (O ∩ E).Nonempty := mem_closure_iff_nhds.mp hp.2 O (hO.mem_nhds hpO)
    let A := e '' (O ∩ E)
    have hA : IsOpen A :=
      e.isOpen_image_of_subset_source (hO.inter hE) (fun _ hx => hx.1.1)
    have hAB : A ⊆ B := by rintro _ ⟨x, hx, rfl⟩; exact hx.1.2
    have hEqA : EqOn (u ∘ e.symm) (v ∘ e.symm) A := by
      rintro _ ⟨x, hx, rfl⟩
      have hUV : u x = v x := (show x ∈ U ∩ {p | u p = v p} from interior_subset hx.2).2
      simpa only [Function.comp_apply, e.left_inv hx.1.1] using hUV
    have hγB : CalderonN.SmoothMetric B γ :=
      ⟨fun i j => (hγ.1 i j).mono hB, fun _ hx => hγ.2 _ (hB hx)⟩
    have hEqB := CalderonN.harmonic_eqOn_of_eqOn_open isOpen_ball (isConnected_ball hr)
      hA (hMeet.image e) hAB hγB ⟨hu.1.mono hB, fun x hx => hu.2 x (hB hx)⟩
        ⟨hv.1.mono hB, fun x hx => hv.2 x (hB hx)⟩ hEqA
    apply interior_maximal _ hO hpO
    intro x hx
    refine ⟨heU hx.1, ?_⟩
    change u x = v x
    simpa only [Function.comp_apply, e.left_inv hx.1] using hEqB hx.2
  have hcover : U ⊆ E ∪ (closure E)ᶜ := fun x hx =>
    or_iff_not_imp_right.mpr (fun h => hclosed ⟨hx, not_not.mp h⟩)
  have hdis : U ∩ (E ∩ (closure E)ᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun _ hx => hx.2.2 (subset_closure hx.2.1)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hConn.2) E (closure E)ᶜ
      hE isClosed_closure.isOpen_compl hcover hdis with h | h
  · exact fun x hx => (show x ∈ U ∩ {p | u p = v p} from interior_subset (h hx)).2
  · obtain ⟨p, hp⟩ := hVne
    exact False.elim ((h (hVU hp)) (subset_closure (hVE hp)))

end CalderonPatch
