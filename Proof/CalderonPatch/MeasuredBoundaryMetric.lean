module

public import Proof.CalderonPatch.PointwiseBoundaryMeasurements

import Mathlib.Tactic

public section
noncomputable section
open Filter Finset MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I Mat MetricField chartVolume metricPair)

variable {n : ℕ}

local notation "Y" => X n
local notation "Z" => X (n+1)
local notation "J" => 𝓡∂ (n+1)
local notation "Qface[" l "," r "]" => Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0)

theorem faceEnergyCoefficient_zero {U : Set Y} {ξ : I n → ℝ} (γ : MetricField (n+1))
    (B : BoundaryLayerCoefficients ξ U) (a : Y → ℝ) (y : Y) :
    faceEnergyCoefficient γ B (fun z => (a z : ℂ)) 0 y =
      a y ^ 2 * (chartVolume γ (normalFacePoint y) * B.kappa y) := by
  rw [faceEnergyCoefficient,B.traceCoefficient_zero]
  simp [Complex.mul_re]
  ring

theorem facePrincipal_eq_principalDensitySymbol {O : Set Z} (hO : IsOpen O)
    {γ : MetricField (n+1)} (hγ : CalderonN.SmoothMetric O γ) (hNN : HasNormalMetricBlock 0 γ O)
    {U : Set Y} (hf : MapsTo normalFacePoint U O)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0) {y : Y} (hy : y ∈ U) :
    let B := boundaryLayerCoefficientsOfMetric hO γ hγ
      (fun x hx => by simpa only [signedLayerCoordinates_face] using hf hx) ξ hξ
    chartVolume γ (normalFacePoint y) * B.kappa y =
      boundaryPrincipalDensitySymbol (tangentialMetricBlock (γ (normalFacePoint y))) (WithLp.toLp 2 ξ) := by
  have hp := hγ.2 _ (hf hy)
  change Real.sqrt (γ (normalFacePoint y)).det * Real.sqrt (faceInverseQuadratic γ ξ y) = _
  unfold boundaryPrincipalDensitySymbol
  rw [det_eq_tangentialMetricBlock (hNN _ (hf hy)),
    ← tangentialMetricBlock_inverse hNN (hf hy) hp]
  simp only [faceInverseQuadratic,signedLayerCoordinates_face,metricPair,
    tangentialMetricBlock,Matrix.submatrix_apply]

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

variable {d₁ d₂ : DirichletData n M} {p₁ p₂ : M}
  (D₁ : NativeBoundaryMetricChart d₁.metric p₁) (D₂ : NativeBoundaryMetricChart d₂.metric p₂)

/-- The principal measurement determines the full metric values in
paired normal charts along the measured face in dimension at least three. -/
theorem field_eqOn_face_of_patchEnergy (hn : 2 ≤ n)
    {Γ : Set ((J).boundary M)} (hMeas : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {l r : I (n+1) → ℝ} (hlr : l ≤ r) (hl0 : l 0 = 0)
    {O : Set Z} (hO : IsOpen O) (hOD₁ : O ⊆ D₁.ambient) (hOD₂ : O ⊆ D₂.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) O)
    (hSame : EqOn D₁.coord.symm D₂.coord.symm (O ∩ {z | z 0 = 0}))
    (hΓ : MapsTo (D₁.coord.symm ∘ normalFacePoint) (tangentialBox l r) (Subtype.val '' Γ))
    {U : Set Y} (hU : IsOpen U)
    (hFace₁ : MapsTo normalFacePoint U D₁.ambient) (hFace₂ : MapsTo normalFacePoint U D₂.ambient)
    (hQU : MapsTo (WithLp.toLp 2) Qface[l,r] U)
    (η : ContDiffBump (0 : ℝ)) (hTop : η.rOut < r 0) :
    EqOn (D₁.field ∘ normalFacePoint) (D₂.field ∘ normalFacePoint) (tangentialBox l r) := by
  let V := tangentialBox l r
  have hVU : V ⊆ U := by
    intro y hy
    have hy' : WithLp.ofLp y ∈ Qface[l,r] :=
      ⟨fun i => (hy i).1.le, fun i => (hy i).2.le⟩
    simpa only [WithLp.toLp_ofLp] using hQU hy'
  have hLead (ξ : I n → ℝ) (hξ : ξ ≠ 0) :
      EqOn (fun y => boundaryPrincipalDensitySymbol (tangentialMetricBlock (D₁.field (normalFacePoint y)))
        (WithLp.toLp 2 ξ))
        (fun y => boundaryPrincipalDensitySymbol (tangentialMetricBlock (D₂.field (normalFacePoint y)))
        (WithLp.toLp 2 ξ)) V := by
    let B₁ := boundaryLayerCoefficientsOfMetric D₁.open_ambient D₁.field D₁.smooth_field
      (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₁ hy) ξ hξ
    let B₂ := boundaryLayerCoefficientsOfMetric D₂.open_ambient D₂.field D₂.smooth_field
      (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₂ hy) ξ hξ
    let C₁ (y : Y) := chartVolume D₁.field (normalFacePoint y) * B₁.kappa y
    let C₂ (y : Y) := chartVolume D₂.field (normalFacePoint y) * B₂.kappa y
    have hC₁ : ContinuousOn C₁ U :=
      ((CalderonN.contDiffOn_metric_volume D₁.smooth_field).continuousOn.comp
        continuous_normalFacePoint.continuousOn hFace₁).mul B₁.kappa_smooth.continuousOn
    have hC₂ : ContinuousOn C₂ U :=
      ((CalderonN.contDiffOn_metric_volume D₂.smooth_field).continuousOn.comp
        continuous_normalFacePoint.continuousOn hFace₂).mul B₂.kappa_smooth.continuousOn
    have hc := eqOn_faceCoefficientDifference_zero_of_patchEnergy D₁ D₂ hMeas hlr hl0 hO
      hOD₁ hOD₂ hBox hSame hΓ hU hFace₁ hFace₂ hQU ξ hξ η hTop 0
      ((hC₁.sub hC₂).mono hVU) (by
        dsimp only
        intro a ha hac hs y hy
        simp only [faceEnergyCoefficient_zero,C₁,C₂,B₁,B₂,Pi.sub_apply,mul_sub])
    intro y hy
    have hC : C₁ y = C₂ y := sub_eq_zero.mp (hc hy)
    exact (facePrincipal_eq_principalDensitySymbol D₁.open_ambient D₁.smooth_field D₁.normal_field
      hFace₁ ξ hξ (hVU hy)).symm.trans (hC.trans
        (facePrincipal_eq_principalDensitySymbol D₂.open_ambient D₂.smooth_field D₂.normal_field
          hFace₂ ξ hξ (hVU hy)))
  intro y hy
  have hp₁ := D₁.smooth_field.2 _ (hFace₁ (hVU hy))
  have hp₂ := D₂.smooth_field.2 _ (hFace₂ (hVU hy))
  apply normalMetric_eq_of_tangentialMetricBlock_eq hp₁.isHermitian.isSymm hp₂.isHermitian.isSymm
    (D₁.normal_field _ (hFace₁ (hVU hy))) (D₂.normal_field _ (hFace₂ (hVU hy)))
  apply boundaryMetric_eq_of_principalDensitySymbol_eq hn
    (tangentialMetricBlock_posDef hp₁) (tangentialMetricBlock_posDef hp₂)
  intro ξ
  by_cases hξ : ξ = 0
  · simp [hξ,boundaryPrincipalDensitySymbol,metricPair]
  have hξ' : (WithLp.ofLp ξ : I n → ℝ) ≠ 0 := by
    intro h
    apply hξ
    apply WithLp.ofLp_injective
    exact h
  simpa only [WithLp.toLp_ofLp,Function.comp_apply] using hLead _ hξ' hy

end CalderonPatch.BoundaryLayer
