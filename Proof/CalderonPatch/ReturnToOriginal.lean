module

public import Proof.CalderonPatch.NormalFlowCompletion

public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M N₁ N₂ : Type*}
  [TopologicalSpace M] [CompactSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M]
  [TopologicalSpace N₁] [T2Space N₁] [ChartedSpace (EuclideanHalfSpace n) N₁]
  [IsManifold (𝓡∂ n) ∞ N₁]
  [TopologicalSpace N₂] [T2Space N₂] [ChartedSpace (EuclideanHalfSpace n) N₂]
  [IsManifold (𝓡∂ n) ∞ N₂]

local notation "J" => 𝓡∂ n

/-- An original manifold embedded in its attached extension. Removing
the closure of the open cap from the extended interior leaves exactly
the image of the original interior. -/
structure OriginalCopy {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]
    [IsManifold (𝓡∂ n) ∞ N] (g : SmoothMetric n M) (gExt : SmoothMetric n N) (cap : Set N) where
  embed : M → N
  inverse : N → M
  left_inv : Function.LeftInverse inverse embed
  smooth : ContMDiff J J ∞ embed
  smooth_inverse : ContMDiffOn J J ∞ inverse (range embed)
  interior_image : embed '' (J).interior M = (J).interior N \ closure cap
  metric : ∀ p (v w : TangentSpace J p), g.inner p v w =
    gExt.inner (embed p) (mfderiv J J embed p v) (mfderiv J J embed p w)

theorem OriginalCopy.closure_image_interior {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace (EuclideanHalfSpace n) N] [IsManifold (𝓡∂ n) ∞ N]
    {g : SmoothMetric n M} {gExt : SmoothMetric n N} {cap : Set N}
    (C : OriginalCopy g gExt cap) : closure (C.embed '' (J).interior M) = range C.embed := by
  apply le_antisymm
  · exact closure_minimal (image_subset_range _ _) (isCompact_range C.smooth.continuous).isClosed
  · rintro _ ⟨x, rfl⟩
    exact image_closure_subset_closure_image C.smooth.continuous
      (mem_image_of_mem _ (dense_manifoldInterior (n := n) (M := M) x))

omit [CompactSpace M] in
private theorem OriginalCopy.right_inv {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n) N] [IsManifold (𝓡∂ n) ∞ N]
    {g : SmoothMetric n M} {gExt : SmoothMetric n N} {cap : Set N} (C : OriginalCopy g gExt cap) :
    EqOn (C.embed ∘ C.inverse) id (range C.embed) := by
  rintro _ ⟨x, rfl⟩
  rw [Function.comp_apply, C.left_inv x, id_eq]

/-- The completed extended isometry matches the original copies by the
interior-complement identity. Its restriction is a smooth metric isometry
and fixes the attached seam wherever the extended map matches the embeds. -/
theorem restrict_completed_isometry_to_original {g₁ g₂ : SmoothMetric n M}
    {gExt₁ : SmoothMetric n N₁} {gExt₂ : SmoothMetric n N₂} {cap₁ : Set N₁} {cap₂ : Set N₂}
    (C₁ : OriginalCopy g₁ gExt₁ cap₁) (C₂ : OriginalCopy g₂ gExt₂ cap₂)
    (Φ : N₂ ≃ₘ⟮J, J⟯ N₁) (hCap : Φ '' cap₂ = cap₁)
    (hMetric : ∀ (x : N₂) (v w : TangentSpace J x), gExt₂.inner x v w =
      gExt₁.inner (Φ x) (mfderiv J J Φ x v) (mfderiv J J Φ x w))
    {P : Set ((J).boundary M)} (hP : ∀ p ∈ P, Φ (C₂.embed p) = C₁.embed p) :
    ∃ Ψ : M ≃ₘ⟮J, J⟯ M, FixesPatch P Ψ ∧ PullbackMetric g₁ g₂ Ψ ∧
      C₁.embed ∘ Ψ = Φ ∘ C₂.embed := by
  have hInt : Φ '' (J).interior N₂ = (J).interior N₁ := by
    have h := Φ.image_boundary (by simp)
    rw [← (J).compl_interior, ← (J).compl_interior,
      image_compl_eq (f := (Φ : N₂ → N₁)) Φ.bijective] at h
    exact compl_injective h
  have hCl (s : Set N₂) : Φ '' closure s = closure (Φ '' s) := Φ.toHomeomorph.image_closure s
  have hOrigInt : Φ '' (C₂.embed '' (J).interior M) = C₁.embed '' (J).interior M := by
    rw [C₂.interior_image, C₁.interior_image, image_sdiff (f := (Φ : N₂ → N₁)) Φ.injective,
      hInt, hCl, hCap]
  have hOrig : Φ '' range C₂.embed = range C₁.embed := by
    rw [← C₂.closure_image_interior, ← C₁.closure_image_interior, hCl, hOrigInt]
  have hMaps₁ : MapsTo Φ (range C₂.embed) (range C₁.embed) := by
    intro y hy
    rw [← hOrig]
    exact mem_image_of_mem _ hy
  have hMaps₂ : MapsTo Φ.symm (range C₁.embed) (range C₂.embed) := by
    intro y hy
    rw [← hOrig] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rwa [Φ.symm_apply_apply]
  let ψ : M → M := C₁.inverse ∘ Φ ∘ C₂.embed
  let ψinv : M → M := C₂.inverse ∘ Φ.symm ∘ C₁.embed
  have hψ (x : M) : C₁.embed (ψ x) = Φ (C₂.embed x) :=
    C₁.right_inv (hMaps₁ (mem_range_self x))
  have hψinv (x : M) : C₂.embed (ψinv x) = Φ.symm (C₁.embed x) :=
    C₂.right_inv (hMaps₂ (mem_range_self x))
  have hLeft : Function.LeftInverse ψinv ψ := by
    intro x
    apply C₂.left_inv.injective
    rw [hψinv, hψ, Φ.symm_apply_apply]
  have hRight : Function.RightInverse ψinv ψ := by
    intro x
    apply C₁.left_inv.injective
    rw [hψ, hψinv, Φ.apply_symm_apply]
  have hS : ContMDiff J J ∞ ψ := C₁.smooth_inverse.comp_contMDiff
    (Φ.contMDiff.comp C₂.smooth) (fun x => hMaps₁ (mem_range_self x))
  have hSi : ContMDiff J J ∞ ψinv := C₂.smooth_inverse.comp_contMDiff
    (Φ.symm.contMDiff.comp C₁.smooth) (fun x => hMaps₂ (mem_range_self x))
  let Ψ : M ≃ₘ⟮J, J⟯ M :=
    { toFun := ψ, invFun := ψinv, left_inv := hLeft, right_inv := hRight,
      contMDiff_toFun := hS, contMDiff_invFun := hSi }
  refine ⟨Ψ, ?_, ?_, funext hψ⟩
  · intro p hp
    apply C₁.left_inv.injective
    exact (hψ p).trans (hP p hp)
  · intro x v w
    have hComp : C₁.embed ∘ ψ = Φ ∘ C₂.embed := funext hψ
    have hD : (mfderiv J J C₁.embed (ψ x)).comp (mfderiv J J ψ x) =
        (mfderiv J J Φ (C₂.embed x)).comp (mfderiv J J C₂.embed x) := by
      rw [← mfderiv_comp x (C₁.smooth.mdifferentiable (by simp) (ψ x)) (hS.mdifferentiable (by simp) x),
        hComp, mfderiv_comp x (Φ.contMDiff.mdifferentiable (by simp) (C₂.embed x))
          (C₂.smooth.mdifferentiable (by simp) x)]
    have hv := congrArg (fun D : TangentSpace J x →L[ℝ] TangentSpace J (C₁.embed (ψ x)) => D v) hD
    have hw := congrArg (fun D : TangentSpace J x →L[ℝ] TangentSpace J (C₁.embed (ψ x)) => D w) hD
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    change g₂.inner x v w = g₁.inner (ψ x) (mfderiv J J ψ x v) (mfderiv J J ψ x w)
    rw [C₂.metric x v w, hMetric, C₁.metric]
    let B (p : N₁) (a b : CalderonN.X n) := gExt₁.inner p a b
    let a₁ (t : TangentSpace J x) : CalderonN.X n := (mfderiv J J C₁.embed (ψ x)) ((mfderiv J J ψ x) t)
    let a₂ (t : TangentSpace J x) : CalderonN.X n :=
      (mfderiv J J Φ (C₂.embed x)) ((mfderiv J J C₂.embed x) t)
    have heq : ((Φ (C₂.embed x), a₂ v, a₂ w) : N₁ × CalderonN.X n × CalderonN.X n) =
        (C₁.embed (ψ x), a₁ v, a₁ w) := Prod.ext (hψ x).symm (Prod.ext hv.symm hw.symm)
    exact congrArg (fun t => B t.1 t.2.1 t.2.2) heq

end CalderonPatch
