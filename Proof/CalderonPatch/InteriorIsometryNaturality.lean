module

public import Proof.CalderonPatch.IsometricCharts
public import Proof.CalderonPatch.ChartDensity
public import Proof.CalderonPatch.ReturnToOriginal

import Mathlib.Tactic
import Proof.CalderonN.GreenWeak

public section
noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (X laplace_congrOn)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ,X n)
local notation "R" => 𝓘(ℝ,ℝ)

variable {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
  {e : OpenPartialHomeomorph M₂ M₁}

omit [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂] in
/-- An interior local isometry transports the native Laplace operator,
using the same coordinate coefficients in transported charts. -/
theorem nativeLaplace_comp_localIsometry (he : IsLocalMetricIsometry g₁ g₂ e)
    (heI₂ : e.source ⊆ (J).interior M₂) (heI₁ : e.target ⊆ (J).interior M₁)
    {u : M₁ → ℝ} (hu : ContMDiffOn J R ∞ u e.target)
    {x : M₂} (hx : x ∈ e.source) :
    nativeLaplace g₂ (u ∘ e) x = nativeLaplace g₁ u (e x) := by
  obtain ⟨b,hxb,hbe,hbI,hb,hbs⟩ := exists_interiorChart x (heI₂ hx) e.open_source hx
  obtain ⟨a,haT,haS,haInv,ha,has,hγ⟩ := exists_transported_chart he b hbe hb hbs
  have hae : a.source ⊆ e.target := by
    rw [haS]
    rw [← e.image_source_eq_target]
    exact image_mono hbe
  have haI := hae.trans heI₁
  have hxa : e x ∈ a.source := haS.symm ▸ mem_image_of_mem e hxb
  have haBx : a (e x) = b x := by
    have hbT := b.map_source hxb
    have haT' : b x ∈ a.target := haT.symm ▸ hbT
    have h := congrFun haInv (b x)
    rw [Function.comp_apply,b.left_inv hxb] at h
    rw [← h,a.right_inv haT']
  have hUE : ContMDiffOn J R ∞ (u ∘ e) b.source :=
    hu.comp (he.smooth.mono hbe) (fun z hz => e.map_source (hbe hz))
  rw [nativeLaplace_eq_coordinate g₂ b hbI hb hbs hUE hxb,
    nativeLaplace_eq_coordinate g₁ a haI ha has (hu.mono hae) hxa,haBx]
  exact (laplace_congrOn b.open_target hγ
    (fun z _ => congrArg u (congrFun haInv z)) (b.map_source hxb)).symm

omit [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂] in
/-- The original embedding restricted to its interior is an actual
open partial homeomorphism and an isometry. -/
theorem OriginalCopy.exists_interiorIsometry [CompactSpace M₂]
    {cap : Set M₁} (C : OriginalCopy g₂ g₁ cap) :
    ∃ e : OpenPartialHomeomorph M₂ M₁, e.source = (J).interior M₂ ∧
      e.target = (J).interior M₁ \ closure cap ∧ (e : M₂ → M₁) = C.embed ∧
      (e.symm : M₁ → M₂) = C.inverse ∧ IsLocalMetricIsometry g₁ g₂ e := by
  let A := (J).interior M₂
  let B := (J).interior M₁ \ closure cap
  have hA : IsOpen A := (J).isOpen_interior (n := ∞) (by simp)
  have hB : IsOpen B := ((J).isOpen_interior (n := ∞) (by simp)).sdiff isClosed_closure
  have hAB : C.embed '' A = B := C.interior_image
  have hBi : B ⊆ range C.embed := by rw [← hAB]; exact image_subset_range _ _
  have hBack : MapsTo C.inverse B A := by
    intro z hz
    rw [← hAB] at hz
    obtain ⟨x,hx,rfl⟩ := hz
    rwa [C.left_inv x]
  have hRight : ∀ z ∈ B, C.embed (C.inverse z) = z := by
    intro z hz
    obtain ⟨x,rfl⟩ := hBi hz
    rw [C.left_inv x]
  let F : OpenPartialHomeomorph M₂ M₁ :=
    { toFun := C.embed
      invFun := C.inverse
      source := A
      target := B
      map_source' := fun x hx => hAB ▸ mem_image_of_mem C.embed hx
      map_target' := hBack
      left_inv' := fun x _ => C.left_inv x
      right_inv' := hRight
      continuousOn_toFun := C.smooth.continuous.continuousOn
      continuousOn_invFun := C.smooth_inverse.continuousOn.mono hBi
      open_source := hA
      open_target := hB }
  exact ⟨F,rfl,rfl,rfl,rfl,⟨C.smooth.contMDiffOn,C.smooth_inverse.mono hBi,fun x _ => C.metric x⟩⟩

end CalderonPatch
