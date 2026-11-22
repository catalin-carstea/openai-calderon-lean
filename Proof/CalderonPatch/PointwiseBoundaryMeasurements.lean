module

public import Proof.CalderonPatch.PairedMeasuredWaves
public import Proof.CalderonPatch.TangentialMetricBlock

import Proof.CalderonPatch.BoundarySquareTests
import Mathlib.Tactic

public section
noncomputable section
open Filter Finset MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I Mat MetricField chartVolume metricPair)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "Y" => X n
local notation "Z" => X (n+1)
local notation "J" => 𝓡∂ (n+1)
local notation "Qface[" l "," r "]" => Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0)

private theorem tangentialBox_subset_closed {l r : I (n+1) → ℝ} :
    tangentialBox l r ⊆ WithLp.ofLp ⁻¹' Qface[l,r] :=
  fun _ h => ⟨fun i => (h i).1.le,fun i => (h i).2.le⟩

variable {d₁ d₂ : DirichletData n M} {p₁ p₂ : M}
  (D₁ : NativeBoundaryMetricChart d₁.metric p₁) (D₂ : NativeBoundaryMetricChart d₂.metric p₂)

/-- When the difference at a given order is a scalar coefficient
times the squared amplitude, the measured energy determines that
coefficient pointwise on the measured face. -/
theorem eqOn_faceCoefficientDifference_zero_of_patchEnergy
    {Γ : Set ((J).boundary M)} (hMeas : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {l r : I (n+1) → ℝ} (hlr : l ≤ r) (hl0 : l 0 = 0)
    {O : Set Z} (hO : IsOpen O) (hOD₁ : O ⊆ D₁.ambient) (hOD₂ : O ⊆ D₂.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) O)
    (hSame : EqOn D₁.coord.symm D₂.coord.symm (O ∩ {z | z 0 = 0}))
    (hΓ : MapsTo (D₁.coord.symm ∘ normalFacePoint) (tangentialBox l r) (Subtype.val '' Γ))
    {U : Set Y} (hU : IsOpen U)
    (hFace₁ : MapsTo normalFacePoint U D₁.ambient) (hFace₂ : MapsTo normalFacePoint U D₂.ambient)
    (hQU : MapsTo (WithLp.toLp 2) Qface[l,r] U)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0)
    (η : ContDiffBump (0 : ℝ)) (hTop : η.rOut < r 0) (k : ℕ)
    {c : Y → ℝ} (hc : ContinuousOn c (tangentialBox l r))
    (hDiff :
      let B₁ := boundaryLayerCoefficientsOfMetric D₁.open_ambient D₁.field D₁.smooth_field
        (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₁ hy) ξ hξ
      let B₂ := boundaryLayerCoefficientsOfMetric D₂.open_ambient D₂.field D₂.smooth_field
        (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₂ hy) ξ hξ
      ∀ a : Y → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ tangentialBox l r →
        ∀ y ∈ tangentialBox l r,
          faceEnergyCoefficient D₁.field B₁ (fun z => (a z : ℂ)) k y -
          faceEnergyCoefficient D₂.field B₂ (fun z => (a z : ℂ)) k y = a y ^ 2 * c y) :
    EqOn c 0 (tangentialBox l r) := by
  let B₁ := boundaryLayerCoefficientsOfMetric D₁.open_ambient D₁.field D₁.smooth_field
    (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₁ hy) ξ hξ
  let B₂ := boundaryLayerCoefficientsOfMetric D₂.open_ambient D₂.field D₂.smooth_field
    (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₂ hy) ξ hξ
  let S : Set Y := WithLp.ofLp ⁻¹' Qface[l,r]
  let V := tangentialBox l r
  have hVS : V ⊆ S := tangentialBox_subset_closed
  have hSU : S ⊆ U := fun y hy => by simpa only [WithLp.toLp_ofLp] using hQU hy
  apply eqOn_of_squared_test_pairings (isOpen_tangentialBox l r) hVS hc continuousOn_const
  intro a ha hac has
  let b (y : Y) : ℂ := a y
  have hb : ContDiffOn ℝ ∞ b U := (Complex.ofRealCLM.contDiff.comp ha).contDiffOn
  let K := tsupport a
  have hK : IsCompact K := hac
  have hb0 : ∀ y ∉ K, b y = 0 := fun y hy => by
    simp [b,image_eq_zero_of_notMem_tsupport hy]
  let Q := Qface[l,r]
  let P₁ (y : Y) := faceEnergyCoefficient D₁.field B₁ b k y
  let P₂ (y : Y) := faceEnergyCoefficient D₂.field B₂ b k y
  have hI₁ : IntegrableOn (fun z : I n → ℝ => P₁ (WithLp.toLp 2 z)) Q volume :=
    ((continuousOn_faceEnergyCoefficient hU D₁.smooth_field hFace₁ B₁ hK.isClosed b hb hb0 k).comp
      (PiLp.continuous_toLp 2 (fun _ : I n => ℝ)).continuousOn hQU).integrableOn_compact isCompact_Icc
  have hI₂ : IntegrableOn (fun z : I n → ℝ => P₂ (WithLp.toLp 2 z)) Q volume :=
    ((continuousOn_faceEnergyCoefficient hU D₂.smooth_field hFace₂ B₂ hK.isClosed b hb hb0 k).comp
      (PiLp.continuous_toLp 2 (fun _ : I n => ℝ)).continuousOn hQU).integrableOn_compact isCompact_Icc
  have hI := integral_faceEnergyCoefficient_eq_of_patchEnergy D₁ D₂ hMeas hlr hl0 hO hOD₁ hOD₂ hBox
    hSame hΓ hU hFace₁ hFace₂ hQU ξ hξ hK (has.trans (hVS.trans hSU)) has b hb hb0 η hTop k
  have hIeq : ∫ z in Q, P₁ (WithLp.toLp 2 z) - P₂ (WithLp.toLp 2 z) = 0 := by
    rw [integral_sub hI₁ hI₂,hI,sub_self]
  have hPoint (y : Y) : a y ^ 2 * c y = P₁ y - P₂ y := by
    by_cases hy : y ∈ V
    · exact (hDiff a ha hac has y hy).symm
    · have hyK : y ∉ K := fun h => hy (has h)
      have h := image_eq_zero_of_notMem_tsupport hyK
      simp [P₁,P₂,faceEnergyCoefficient,hb0 y hyK,h]
  have hTransform (f : Y → ℝ) :
      (∫ z in Q, f (WithLp.toLp 2 z)) = ∫ y in S, f y := by
    let L := MeasurableEquiv.toLp 2 (I n → ℝ)
    have hPre : L ⁻¹' S = Q := by
      ext z
      simp [S,Q,L]
    rw [← hPre]
    exact (PiLp.volume_preserving_toLp (I n)).setIntegral_preimage_emb L.measurableEmbedding f S
  change (∫ x in S, a x ^ 2 * c x) = ∫ x in S, a x ^ 2 * (0 : ℝ)
  simp only [mul_zero,integral_zero]
  rw [← hTransform (fun y => a y ^ 2 * c y), ← hIeq]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => hPoint _)

end CalderonPatch.BoundaryLayer
