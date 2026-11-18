import Mathlib.Topology.ContinuousOn

set_option autoImplicit false
open Set Filter
namespace OAI.AnisotropicCalderon

/-- Shrink an open neighborhood around a fixed point of a continuous
    idempotent normalization so that normalization preserves it. -/
theorem exists_normalization_stable_neighborhood {P : Type*} [TopologicalSpace P]
    (N : P → P) (D W : Set P) (hD : IsOpen D) (hW : IsOpen W)
    (hN : ContinuousOn N D) (hWD : W ⊆ D)
    (hIdem : ∀ p ∈ D,N (N p) = N p) (p0 : P) (hp : p0 ∈ W) (hFix : N p0 = p0) :
    ∃ V : Set P,IsOpen V ∧ p0 ∈ V ∧ V ⊆ W ∧ ∀ p ∈ V,N p ∈ V := by
  let V := W ∩ N ⁻¹' W
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hpV
    have hc : ContinuousAt N p := (hN p (hWD hpV.1)).continuousAt (hD.mem_nhds (hWD hpV.1))
    exact inter_mem (hW.mem_nhds hpV.1) (hc.preimage_mem_nhds (hW.mem_nhds hpV.2))
  refine ⟨V,hV,⟨hp,?_⟩,(fun _ h => h.1),?_⟩
  · change N p0 ∈ W
    rw [hFix]
    exact hp
  · intro p hpV
    refine ⟨hpV.2,?_⟩
    change N (N p) ∈ W
    rw [hIdem p (hWD hpV.1)]
    exact hpV.2

end OAI.AnisotropicCalderon
