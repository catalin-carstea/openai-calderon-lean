module

public import Proof.CalderonPatch.CapShift

public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

local notation "J" => 𝓡∂ n

omit [IsManifold (𝓡∂ n) ∞ M] [FiniteDimensional ℝ Z] in
/-- The trace on the original boundary of a function vanishing at
the extended boundary is supported in the patch of the cap shift. -/
theorem CapShift.trace_support_subset {D : ProductBoundaryChart (n := n) (M := M) (Z := Z)}
    (C : CapShift D) {Γ : Set ((J).boundary M)}
    (hΓ : (Subtype.val : (J).boundary M → M) ⁻¹' C.support ⊆ Γ)
    {w : M → ℝ} (hw : EqOn w 0 ((J).boundary M)) :
    tsupport (fun p : (J).boundary M => w (C.embed p)) ⊆ Γ := by
  apply (closure_minimal _ (C.closed_support.preimage continuous_subtype_val)).trans hΓ
  intro p hp
  by_contra h
  have he : C.embed p = p := C.embed_eq_id_off_support h
  apply hp
  change w (C.embed p) = 0
  rw [he]
  exact hw p.property

end CalderonPatch
