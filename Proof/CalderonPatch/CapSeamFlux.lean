module

public import Proof.CalderonPatch.CapBoundaryTests
public import Proof.CalderonPatch.MeasuredCapFlux

import Mathlib.Tactic

public section
noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X axis chartVolume coordDeriv divergenceFlux)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (n+1)
local notation "E" => X N
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

variable {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}
  {C : MeasuredCommonCap d₁ d₂ Γ}

namespace MeasuredCommonCap

/-- The outward flux from the cap across the original seam is
nonpositive for the truncated difference test. The normal used
in the original measurements has the opposite orientation. -/
theorem ScalarReadings.truncated_seamFlux_nonpos
    (hMeas : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {w₁ w₂ : M → ℝ} (D : C.ScalarReadings w₁ w₂)
    (hw₁ : ContMDiff J R ∞ w₁) (hw₂ : ContMDiff J R ∞ w₂)
    (hw₁₀ : EqOn w₁ 0 ((J).boundary M)) (hw₂₀ : EqOn w₂ 0 ((J).boundary M))
    (hH₁ : EqOn (nativeLaplace d₁.metric (w₁ ∘ C.firstCopy.embed)) 0 ((J).interior M))
    (hH₂ : EqOn (nativeLaplace d₂.metric (w₂ ∘ C.secondCopy.embed)) 0 ((J).interior M))
    (hSolve₁ : ∀ v : M → ℝ, ContMDiff J R ∞ v →
      ∃ w : M → ℝ, ContMDiff J R ∞ w ∧ EqOn w v ((J).boundary M) ∧
        EqOn (nativeLaplace d₁.metric w) 0 ((J).interior M))
    (hSolve₂ : ∀ v : M → ℝ, ContMDiff J R ∞ v →
      ∃ w : M → ℝ, ContMDiff J R ∞ w ∧ EqOn w v ((J).boundary M) ∧
        EqOn (nativeLaplace d₂.metric w) 0 ((J).interior M)) :
    ∀ ε > 0,
      (∫ z in Icc (C.coordinates.box.lower ∘ Fin.succAbove 0) (C.capUpper ∘ Fin.succAbove 0),
        capTraceCutoff ε ((D.first-D.second) (normalFacePoint (WithLp.toLp 2 z))) *
          divergenceFlux C.coordinates.first.field (D.first-D.second)
            (normalFacePoint (WithLp.toLp 2 z)) 0) ≤ 0 := by
  intro ε hε
  let A₁ := C.charts.first
  let A₂ := C.charts.second
  let v₁ := w₁ ∘ C.firstCopy.embed
  let v₂ := w₂ ∘ C.secondCopy.embed
  let g := C.coordinates.first.field
  let δ := D.first - D.second
  let a := C.originalLower
  let b := C.coordinates.box.upper
  let S := tangentialBox a b
  have hv₁ : ContMDiff J R ∞ v₁ := hw₁.comp C.firstCopy.smooth
  have hv₂ : ContMDiff J R ∞ v₂ := hw₂.comp C.secondCopy.smooth
  have hUD₁ : D.domain ⊆ A₁.ambient := D.domain_subset.trans C.nativeAmbient_first
  have hUD₂ : D.domain ⊆ A₂.ambient := D.domain_subset.trans C.nativeAmbient_second
  obtain ⟨f,φ,hf,hfC,hfS,hfT,hφ,hTrace₁,hTrace₂⟩ :=
    D.exists_truncated_trace_test hw₁₀ hw₂₀ hε
  have hRead₁ := D.original_first
  have hRead₂ := D.original_second
  have hBox := C.mapsTo_originalBox D.box_subset
  have hNonneg := integral_sub_outwardConormal_nonneg_of_patchEnergy d₁.metric_volume d₂.metric_volume
    hMeas A₁ A₂ C.originalLower_le C.originalLower_normal D.open_domain hUD₁ hUD₂ hBox
    hv₁ hv₂ hH₁ hH₂ (C.traces_supported _ hw₁₀).1 (C.traces_supported _ hw₂₀).2
    D.smooth_first.contDiffOn D.smooth_second.contDiffOn hRead₁ hRead₂ hε hf hfC hfS hfT
    hTrace₁ hTrace₂ hSolve₁ hSolve₂
  have hTop : ∀ z ∈ S, capTraceCutoff ε (δ (normalFacePoint z)) *
        divergenceFlux g δ (normalFacePoint z) 0 =
      -(φ z * (A₁.outwardConormalDensity v₁ z - A₂.outwardConormalDensity v₂ z)) := by
    intro z hz
    let x := normalFacePoint z
    have hCoord : WithLp.ofLp x ∈ Icc a b := normalFacePoint_in_closedBox C.originalLower_normal
      (C.coordinates.box.radius_pos.trans C.coordinates.box.top_lt).le
      ⟨fun i => (hz i).1.le,fun i => (hz i).2.le⟩
    have hx : x ∈ D.domain := by
      have h := hBox hCoord
      rwa [WithLp.toLp_ofLp] at h
    have hx₀ : x 0 = 0 := normalFacePoint_height z
    have hxH : x ∈ H := (mem_inwardHalfSpace).mpr hx₀.ge
    have hG₁ : g x = A₁.field x := C.coordinates.first.inward_field hxH
    have hG₂ : A₁.field x = A₂.field x := C.coordinates.original_fields_eq ⟨D.domain_subset hx,hx₀⟩
    have hFlux : divergenceFlux g δ x 0 = chartVolume A₁.field x * coordDeriv 0 δ x := by
      have hInv (j : I N) : (g x)⁻¹ 0 j = if (0 : I N) = j then 1 else 0 := by
        rw [hG₁]
        exact inverse_normalMetricBlock_row A₁.normal_field (hUD₁ hx) (A₁.smooth_field.2 _ (hUD₁ hx)) j
      have hVol : chartVolume g x = chartVolume A₁.field x := by simp only [chartVolume,hG₁]
      simp only [divergenceFlux,CalderonN.divergenceCoeff,hVol,hInv,
        mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hIn₁ := A₁.inwardDerivative_eq_coordDeriv D.open_domain D.smooth_first.contDiffOn hRead₁ ⟨hx,hxH⟩
    have hIn₂ := A₂.inwardDerivative_eq_coordDeriv D.open_domain D.smooth_second.contDiffOn hRead₂ ⟨hx,hxH⟩
    have hVol₂ : chartVolume A₂.field x = chartVolume A₁.field x := by simp only [chartVolume,hG₂]
    have hDer : coordDeriv 0 δ x = coordDeriv 0 D.first x - coordDeriv 0 D.second x := by
      change fderiv ℝ (D.first-D.second) x (axis 0) = _
      rw [fderiv_sub (D.smooth_first.differentiable (by simp) x)
        (D.smooth_second.differentiable (by simp) x)]
      rfl
    change (capTraceCutoff ε (δ x)) * divergenceFlux g δ x 0 =
      -(φ z * (-(chartVolume A₁.field x * A₁.inwardDerivative v₁ x) -
        -(chartVolume A₂.field x * A₂.inwardDerivative v₂ x)))
    rw [hFlux,← hφ z hx,hIn₁,hIn₂,hVol₂,hDer]
    ring
  let F (z : X n) := capTraceCutoff ε (δ (normalFacePoint z)) *
    divergenceFlux g δ (normalFacePoint z) 0
  let Q := Set.pi univ (fun j : I n => Ioo ((a ∘ Fin.succAbove 0) j) ((b ∘ Fin.succAbove 0) j))
  have ha : a ∘ Fin.succAbove 0 = C.coordinates.box.lower ∘ Fin.succAbove 0 := by
    funext i
    simp [a,MeasuredCommonCap.originalLower]
  rw [C.capUpper_tangential,← ha]
  change (∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0), F (WithLp.toLp 2 z)) ≤ 0
  rw [setIntegral_congr_set (show (Icc _ _ : Set (I n → ℝ)) =ᵐ[volume] Q from
    Measure.univ_pi_Ioo_ae_eq_Icc.symm)]
  let l := MeasurableEquiv.toLp 2 (I n → ℝ)
  have hEq : l ⁻¹' S = Q := by
    ext z
    simp [tangentialBox,S,Q,Set.mem_pi,l]
  have hPush : (∫ z in l ⁻¹' S, F (WithLp.toLp 2 z)) = ∫ z in S, F z :=
    (PiLp.volume_preserving_toLp (I n)).setIntegral_preimage_emb l.measurableEmbedding F S
  rw [← hEq,hPush]
  rw [setIntegral_congr_fun (isOpen_tangentialBox _ _).measurableSet hTop,integral_neg]
  exact neg_nonpos.mpr hNonneg

end MeasuredCommonCap

end CalderonPatch
