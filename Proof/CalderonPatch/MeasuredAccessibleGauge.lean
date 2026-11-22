module

public import Proof.CalderonPatch.DirichletHilbert
public import Proof.CalderonPatch.GaugeInCommonNormals
public import Proof.CalderonPatch.BoundaryFluxPairing
public import Proof.CalderonPatch.PairedNativeBoundaryBox

import Proof.CalderonPatch.MeasuredBoundaryMetric
import Proof.CalderonPatch.NativeInverseRegularityProof
import Proof.CalderonPatch.SmoothDirichletFromForcing
import Mathlib.Tactic.Linarith

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X chartVolume)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "N" => (n+1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N
local notation "E" => X N
local notation "Y" => X n

section Dirichlet

variable [PreconnectedSpace M]

private theorem exists_harmonic_trace_extension (D : DirichletData n M)
    {f : M → ℝ} (hf : ContMDiff J R ∞ f) :
    ∃ u : M → ℝ, ContMDiff J R ∞ u ∧ EqOn u f ((J).boundary M) ∧
      EqOn (nativeLaplace D.metric u) 0 ((J).interior M) :=
  exists_dirichletHarmonic_from_smoothForcing D (fun f q hq hf => by
    obtain ⟨u,hu,hU,hEq,_⟩ := (nativeInverseRegularity D).smooth_solution f q hq hf
    exact ⟨u,hu,hU,hEq⟩) hf

/-- The measured conormal and the determined surface density give
the inward unit-normal derivative on the common coordinate face. -/
theorem PairedNativeBoundaryBox.inwardDerivative_eventuallyEq_of_patchEnergy
    (hn : 2 ≤ n) {d₁ d₂ : DirichletData n M} {Γ : Set ((J).boundary M)}
    {p : (J).boundary M} (B : PairedNativeBoundaryBox d₁.metric d₂.metric Γ p)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {u₁ u₂ : M → ℝ} (hu₁ : ContMDiff J R ∞ u₁) (hu₂ : ContMDiff J R ∞ u₂)
    (hH₁ : EqOn (nativeLaplace d₁.metric u₁) 0 ((J).interior M))
    (hH₂ : EqOn (nativeLaplace d₂.metric u₂) 0 ((J).interior M))
    (hTrace : EqOn u₁ u₂ ((J).boundary M))
    (hSupp : tsupport (fun x : (J).boundary M => u₁ x) ⊆ Γ) :
    B.first.inwardDerivative u₁ =ᶠ[𝓝[{z : E | z (0 : I N) = 0}] (B.second.coord p)]
      B.second.inwardDerivative u₂ := by
  let C := WithLp.toLp 2 '' Icc B.boxLower B.boxUpper
  have hC : IsCompact C := (isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : I N => ℝ)))
  have hCS : C ⊆ B.signed := by
    rintro _ ⟨z,hz,rfl⟩
    exact B.closed_box hz
  obtain ⟨r₁,V₁,hr₁,hV₁,hCV₁,_,hR₁⟩ :=
    B.first.exists_smooth_function_extension hu₁ hC (hCS.trans B.signed₁)
  obtain ⟨r₂,V₂,hr₂,hV₂,hCV₂,_,hR₂⟩ :=
    B.second.exists_smooth_function_extension hu₂ hC (hCS.trans B.signed₂)
  let U := B.signed ∩ (V₁ ∩ V₂)
  have hU : IsOpen U := B.open_signed.inter (hV₁.inter hV₂)
  have hCU : C ⊆ U := fun z hz => ⟨hCS hz,hCV₁ hz,hCV₂ hz⟩
  have hUS : U ⊆ B.signed := inter_subset_left
  have hBox : MapsTo (WithLp.toLp 2) (Icc B.boxLower B.boxUpper) U :=
    fun z hz => hCU (mem_image_of_mem _ hz)
  have hSolve (v : M → ℝ) (hv : ContMDiff J R ∞ v)
      (_ : tsupport (fun x : (J).boundary M => v x) ⊆ Γ) :
      ∃ w₁ w₂ : M → ℝ, ContMDiff J R ∞ w₁ ∧ ContMDiff J R ∞ w₂ ∧
        EqOn w₁ v ((J).boundary M) ∧ EqOn w₂ v ((J).boundary M) ∧
        EqOn (nativeLaplace d₁.metric w₁) 0 ((J).interior M) ∧
        EqOn (nativeLaplace d₂.metric w₂) 0 ((J).interior M) := by
    obtain ⟨w₁,hw₁,hT₁,hW₁⟩ := exists_harmonic_trace_extension d₁ hv
    obtain ⟨w₂,hw₂,hT₂,hW₂⟩ := exists_harmonic_trace_extension d₂ hv
    exact ⟨w₁,w₂,hw₁,hw₂,hT₁,hT₂,hW₁,hW₂⟩
  have hConormal := outwardConormalDensity_eq_of_patchEnergy
    d₁.metric_volume d₂.metric_volume hEnergy B.first B.second B.bounds B.lower_zero
    B.upper_pos hU (hUS.trans B.signed₁) (hUS.trans B.signed₂) hBox
    (B.common_inverse.mono (inter_subset_inter_left _ hUS)) B.face_patch
    hu₁ hu₂ hH₁ hH₂ hTrace hSupp hr₁.contDiffOn hr₂.contDiffOn
    (hR₁.symm.mono (inter_subset_inter_left H (fun _ hz => hz.2.1)))
    (hR₂.symm.mono (inter_subset_inter_left H (fun _ hz => hz.2.2))) hSolve
  let A := normalFacePoint ⁻¹' B.signed
  have hA : IsOpen A := B.open_signed.preimage continuous_normalFacePoint
  have hA₁ : MapsTo normalFacePoint A B.first.ambient := fun _ h => B.signed₁ h
  have hA₂ : MapsTo normalFacePoint A B.second.ambient := fun _ h => B.signed₂ h
  have hQA : MapsTo (WithLp.toLp 2)
      (Icc (B.boxLower ∘ Fin.succAbove 0) (B.boxUpper ∘ Fin.succAbove 0)) A := by
    intro z hz
    have hZ : WithLp.ofLp (normalFacePoint (WithLp.toLp 2 z)) ∈ Icc B.boxLower B.boxUpper :=
      normalFacePoint_in_closedBox B.lower_zero B.upper_pos.le hz
    have h := B.closed_box hZ
    rw [WithLp.toLp_ofLp] at h
    exact h
  let η : ContDiffBump (0 : ℝ) := ⟨B.boxUpper 0 / 4,B.boxUpper 0 / 2,
    by linarith only [B.upper_pos],by linarith only [B.upper_pos]⟩
  have hη : η.rOut < B.boxUpper 0 := by
    change B.boxUpper 0 / 2 < B.boxUpper 0
    linarith only [B.upper_pos]
  have hField := BoundaryLayer.field_eqOn_face_of_patchEnergy B.first B.second hn hEnergy
    B.bounds B.lower_zero B.open_signed B.signed₁ B.signed₂ B.closed_box B.common_inverse
    B.face_patch hA hA₁ hA₂ hQA η hη
  have hDeriv (y : Y) (hy : y ∈ tangentialBox B.boxLower B.boxUpper) :
      B.first.inwardDerivative u₁ (normalFacePoint y) =
        B.second.inwardDerivative u₂ (normalFacePoint y) := by
    have hyA : y ∈ A := by
      have h : WithLp.ofLp y ∈ Icc (B.boxLower ∘ Fin.succAbove 0) (B.boxUpper ∘ Fin.succAbove 0) :=
        ⟨fun i => (hy i).1.le,fun i => (hy i).2.le⟩
      simpa only [WithLp.toLp_ofLp] using hQA h
    have hρ : chartVolume B.first.field (normalFacePoint y) =
        chartVolume B.second.field (normalFacePoint y) :=
      congrArg (fun a : CalderonN.Mat N => Real.sqrt a.det) (hField hy)
    have hρp : 0 < chartVolume B.first.field (normalFacePoint y) :=
      Real.sqrt_pos.mpr (B.first.smooth_field.2 _ (hA₁ hyA)).det_pos
    have h := hConormal hy
    rw [NativeBoundaryMetricChart.outwardConormalDensity, NativeBoundaryMetricChart.outwardConormalDensity,
      ← hρ] at h
    exact mul_left_cancel₀ hρp.ne' (neg_injective h)
  have hNear := ((isOpen_tangentialBox B.boxLower B.boxUpper).preimage
    contDiff_normalTangentialCoordinates.continuous).mem_nhds B.center_box
  filter_upwards [mem_nhdsWithin_of_mem_nhds hNear,eventually_mem_nhdsWithin] with z hz hz₀
  have h := hDeriv (normalTangentialCoordinates z) hz
  rwa [normalFacePoint_tangentialCoordinates hz₀] at h

end Dirichlet

variable [ConnectedSpace M]

/-- A native isometry fixed near one point of the measured patch fixes
all of the patch once it preserves the measured Dirichlet energy. -/
theorem fixesPatch_of_patchEnergy_of_fixes_seam (hn : 2 ≤ n)
    (d₁ d₂ : DirichletData n M) {Γ : Set ((J).boundary M)}
    (hΓ : IsOpen Γ)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (Φ : M ≃ₘ⟮J, J⟯ M) (hΦ : PullbackMetric d₁.metric d₂.metric Φ)
    {V : Set M} (hV : IsOpen V) {p : (J).boundary M}
    (hpΓ : p ∈ Γ) (hpV : (p : M) ∈ V)
    (hFix : EqOn Φ id (V ∩ (J).boundary M)) : FixesPatch Γ Φ := by
  obtain ⟨B⟩ := exists_pairedNativeBoundaryBox d₁.metric d₂.metric hΓ hpΓ
  let W := V ∩ (B.second.coord.source ∩ B.second.coord ⁻¹' B.signed)
  have hW : IsOpen W := hV.inter <|
    B.second.smooth.continuousOn.isOpen_inter_preimage B.second.open_source B.open_signed
  have hpW : (p : M) ∈ W := ⟨hpV,B.second.point_source,B.center_signed⟩
  have hCoords : EqOn B.first.coord B.second.coord (W ∩ (J).boundary M) := by
    intro q hq
    exact (B.trace_second ⟨q,hq.2⟩ hq.1.2.1 hq.1.2.2).2.1
  refine fixesPatch_of_native_normalDerivativeAgreement hΓ Φ hΦ p.property
    B.first B.second hW hpW (hFix.mono (inter_subset_inter_left _ inter_subset_left)) hCoords ?_
  intro f hf hfΓ
  obtain ⟨u₁,hu₁,hT₁,hH₁⟩ := exists_harmonic_trace_extension d₁ hf
  obtain ⟨u₂,hu₂,hT₂,hH₂⟩ := exists_harmonic_trace_extension d₂ hf
  have hTrace : EqOn u₁ u₂ ((J).boundary M) := fun q hq => (hT₁ hq).trans (hT₂ hq).symm
  have hUΓ : tsupport (fun x : (J).boundary M => u₁ x) ⊆ Γ := by
    rwa [show (fun x : (J).boundary M => u₁ x) = (fun x : (J).boundary M => f x) from
      funext fun q => hT₁ q.property]
  exact ⟨u₁,u₂,hu₁,hu₂,hT₁,hT₂,hH₁,hH₂,
    B.inwardDerivative_eventuallyEq_of_patchEnergy hn hEnergy hu₁ hu₂ hH₁ hH₂ hTrace hUΓ⟩

/-- The same recovery when the fixed attachment is given as an open
subset of the boundary, as in the native cap construction. -/
theorem fixesPatch_of_patchEnergy_of_fixes_open_subpatch (hn : 2 ≤ n)
    (d₁ d₂ : DirichletData n M) {Γ A : Set ((J).boundary M)}
    (hΓ : IsOpen Γ) (hA : IsOpen A) (hAn : A.Nonempty) (hAΓ : A ⊆ Γ)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (Φ : M ≃ₘ⟮J, J⟯ M) (hΦ : PullbackMetric d₁.metric d₂.metric Φ)
    (hFix : FixesPatch A Φ) : FixesPatch Γ Φ := by
  obtain ⟨p,hp⟩ := hAn
  obtain ⟨V,hV,hVA⟩ := isOpen_induced_iff.mp hA
  have hpV : p ∈ Subtype.val ⁻¹' V := hVA.symm ▸ hp
  refine fixesPatch_of_patchEnergy_of_fixes_seam hn d₁ d₂ hΓ hEnergy Φ hΦ
    hV (hAΓ hp) hpV ?_
  intro q hq
  have hqA : (⟨q,hq.2⟩ : (J).boundary M) ∈ A :=
    hVA ▸ (show (⟨q,hq.2⟩ : (J).boundary M) ∈ Subtype.val ⁻¹' V from hq.1)
  exact hFix ⟨q,hq.2⟩ hqA

end CalderonPatch
