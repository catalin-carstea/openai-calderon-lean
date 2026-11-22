module

public import Proof.CalderonPatch.Energy
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.NhdsSet

public section

open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

/-- Smooth data supported in the measured boundary patch distinguish
each measured point from every other boundary point. -/
theorem exists_supportedTrace_separating {Γ : Set ((𝓡∂ n).boundary M)} (hΓ : IsOpen Γ)
    {p q : (𝓡∂ n).boundary M} (hp : p ∈ Γ) (hpq : p ≠ q) :
    ∃ f : M → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f ∧
      tsupport (fun b : (𝓡∂ n).boundary M => f b) ⊆ Γ ∧ f p = 1 ∧ f q = 0 := by
  obtain ⟨U, hU, hUΓ⟩ := isOpen_induced_iff.mp hΓ
  let V := U ∩ ({(q : M)} : Set M)ᶜ
  have hV : IsOpen V := hU.inter isClosed_singleton.isOpen_compl
  have hpU : p ∈ Subtype.val ⁻¹' U := hUΓ.symm ▸ hp
  have hpV : (p : M) ∈ V := ⟨hpU, fun h => hpq (Subtype.ext (mem_singleton_iff.mp h))⟩
  have hdis : Disjoint Vᶜ ({(p : M)} : Set M) := disjoint_singleton_right.mpr (not_not.mpr hpV)
  obtain ⟨f, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓡∂ n) hV.isClosed_compl isClosed_singleton hdis (n := ⊤)
  have hsupport : tsupport (f : M → ℝ) ⊆ V := by
    intro x hx
    by_contra hout
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hzero.filter_mono (nhds_le_nhdsSet hout))) hx
  have hrestrict : tsupport (fun b : (𝓡∂ n).boundary M => f b) ⊆
      Subtype.val ⁻¹' tsupport (f : M → ℝ) :=
    closure_minimal (fun _ hx => subset_tsupport _ hx) (isClosed_closure.preimage continuous_subtype_val)
  refine ⟨f, f.contMDiff, ?_, hone.self_of_nhdsSet _ (mem_singleton _), ?_⟩
  · intro x hx
    exact hUΓ ▸ (show x ∈ Subtype.val ⁻¹' U from (hsupport (hrestrict hx)).1)
  · exact hzero.self_of_nhdsSet _ (fun h => h.2 (mem_singleton _))

/-- The identities of the original Dirichlet traces recover the gauge on
every measured boundary point, even on components away from the cap. -/
theorem fixesPatch_of_supported_trace_eq {Γ : Set ((𝓡∂ n).boundary M)} (hΓ : IsOpen Γ)
    (Φ : M ≃ₘ⟮𝓡∂ n, 𝓡∂ n⟯ M)
    (hTrace : ∀ f : M → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f →
      tsupport (fun b : (𝓡∂ n).boundary M => f b) ⊆ Γ →
      ∀ b : (𝓡∂ n).boundary M, f b = f (Φ b)) :
    FixesPatch Γ Φ := by
  intro p hp
  by_contra hne
  have hq : Φ p ∈ (𝓡∂ n).boundary M :=
    (Φ.image_boundary (by simp)).subset (mem_image_of_mem Φ p.property)
  let q : (𝓡∂ n).boundary M := ⟨Φ p, hq⟩
  have hpq : p ≠ q := fun h => hne (congrArg Subtype.val h).symm
  obtain ⟨f, hf, hs, hfp, hfq⟩ := exists_supportedTrace_separating hΓ hp hpq
  exact one_ne_zero (hfp.symm.trans ((hTrace f hf hs p).trans hfq))

end CalderonPatch
