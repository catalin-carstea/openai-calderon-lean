module

public import Proof.CalderonPatch.BoundaryWaveFace
public import Proof.CalderonPatch.BoundaryTrialEnergy

import Mathlib.Tactic

public section

noncomputable section
open Filter Finset MeasureTheory Polynomial Set
open scoped ContDiff Manifold

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I MetricField chartVolume coordDeriv)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)
local notation "H" => inwardHalfSpace (n+1)
local notation "J" => 𝓡∂ (n+1)
local notation "R" => 𝓘(ℝ,ℝ)

/-- The density-valued coefficient seen by summing the energies of the
real and imaginary parts of a boundary wave. -/
@[expose] def faceEnergyCoefficient {ξ : I n → ℝ} {U : Set Y} (γ : MetricField (n+1))
    (B : BoundaryLayerCoefficients ξ U) (a : Y → ℂ) (j : ℕ) (y : Y) : ℝ :=
  -(chartVolume γ (normalFacePoint y) * ((starRingEnd ℂ) (a y) * B.traceCoefficient a j y).re)

theorem continuousOn_faceEnergyCoefficient {ξ : I n → ℝ} {U : Set Y} (hU : IsOpen U)
    {O : Set Z} {γ : MetricField (n+1)} (hγ : CalderonN.SmoothMetric O γ)
    (hFace : MapsTo normalFacePoint U O)
    (B : BoundaryLayerCoefficients ξ U) {K : Set Y} (hK : IsClosed K)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) :
    ContinuousOn (faceEnergyCoefficient γ B a j) U := by
  have hP := (B.layerPolynomial_properties hU hK a ha ha0 j).1
  have hT : ContDiffOn ℝ ∞ (B.traceCoefficient a j) U := by
    unfold BoundaryLayerCoefficients.traceCoefficient profileDerivative
    have hκ : ContDiffOn ℝ ∞ (fun y => (B.kappa y : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn B.kappa_smooth
    simpa only [← coeff_zero_eq_eval_zero,coeff_sub,coeff_C_mul] using
      (hP.derivative 0).sub (hκ.mul (hP 0))
  have hVol := (CalderonN.contDiffOn_metric_volume hγ).continuousOn.comp
    continuous_normalFacePoint.continuousOn hFace
  exact (hVol.mul (Complex.continuous_re.comp_continuousOn
    ((Complex.continuous_conj.comp_continuousOn ha.continuousOn).mul hT.continuousOn))).neg

theorem signedLayerCoordinates_mapsTo_halfBox {K : Set Y}
    {l r : I (n+1) → ℝ} (hKbox : K ⊆ tangentialBox l r)
    {ρ : ℝ} (hTop : ρ < r 0) :
    MapsTo signedLayerCoordinates (K ×ˢ Icc 0 ρ) (normalHalfBox l r) := by
  intro w hw
  have hy := hKbox hw.1
  refine ⟨hw.2.1,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [signedLayerCoordinates_height]
      exact hw.2.2.trans_lt hTop
    · rw [signedLayerCoordinates_tangent,← Fin.succAbove_zero]
      exact (hy j).2
  · intro i hi
    obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
    rw [Fin.succAbove_zero,signedLayerCoordinates_tangent,← Fin.succAbove_zero]
    exact (hy j).1

/-- Every component of a finite wave supported in a tangential compact
set and below the top height is a valid half-box test. -/
theorem waveComponent_support_halfBox {ξ : I n → ℝ} {U : Set Y} (hU : IsOpen U)
    (B : BoundaryLayerCoefficients ξ U) {K : Set Y} (hK : IsClosed K)
    {l r : I (n+1) → ℝ} (hKbox : K ⊆ tangentialBox l r)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ)) (hTop : η.rOut < r 0) (N : ℕ) (h : ℝ)
    (L : ℂ →L[ℝ] ℝ) :
    tsupport (L ∘ B.finiteWave a η N h ∘ signedLayerCoordinates.symm) ∩ H ⊆ normalHalfBox l r := by
  intro z hz
  let w := signedLayerCoordinates.symm z
  have he : signedLayerCoordinates w = z := signedLayerCoordinates.apply_symm_apply z
  have hs := B.finiteWave_tsupport_subset hU hK a ha ha0 η N h
    (waveComponent_support L hz.1)
  have ht := hs.2
  rw [η.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,sub_zero] at ht
  have hw₀ : 0 ≤ w.2 := by
    rw [← signedLayerCoordinates_height w,he]
    exact mem_inwardHalfSpace.mp hz.2
  rw [← he]
  exact signedLayerCoordinates_mapsTo_halfBox hKbox hTop ⟨hs.1,hw₀,(le_abs_self _).trans ht⟩

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "Qface[" l "," r "]" => Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0)
local notation "Gpair[" g "," μ "," u "]" =>
  (∫ x, u x * nativeLaplace g u x + covectorEnergy g x (mfderiv J R u x) ∂μ)

/-- The sum of the two native Green pairings, scaled by the reciprocal
frequency, is exactly a polynomial of weighted face integrals. -/
theorem finiteWave_nativeGreen_polynomial {g : SmoothMetric (n+1) M} {p : M}
    (D : NativeBoundaryMetricChart g p) (μ : Measure M) (hμ : IsMetricVolume g μ)
    {l r : I (n+1) → ℝ} (hlr : l ≤ r) (hl0 : l 0 = 0)
    {O : Set Z} (hO : IsOpen O) (hOD : O ⊆ D.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) O)
    {ξ : I n → ℝ} {U : Set Y} (hU : IsOpen U)
    (hFace : MapsTo normalFacePoint U D.ambient)
    (hQU : MapsTo (WithLp.toLp 2) Qface[l,r] U)
    (B : BoundaryLayerCoefficients ξ U) {K : Set Y}
    (hK : IsCompact K) (hKU : K ⊆ U) (hKbox : K ⊆ tangentialBox l r)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ)) (hTop : η.rOut < r 0) (N : ℕ) {h : ℝ} (hh : h ≠ 0) :
    let V := B.finiteWave a η N h
    let u := nativeWaveComponent D V Complex.reCLM
    let v := nativeWaveComponent D V Complex.imCLM
    h * (Gpair[g,μ,u] + Gpair[g,μ,v]) =
      ∑ j ∈ range (N+1), h ^ j * (∫ z in Qface[l,r],
        faceEnergyCoefficient D.field B a j (WithLp.toLp 2 z)) := by
  let V := B.finiteWave a η N h
  have hV := B.finiteWave_contDiff hU hK.isClosed hKU a ha ha0 η η.contDiff N h
  have hVC := B.finiteWave_hasCompactSupport hU hK a ha ha0 η η.hasCompactSupport N h
  let zface (z : I n → ℝ) := normalFacePoint (WithLp.toLp 2 z)
  let Q := Qface[l,r]
  let read (L : ℂ →L[ℝ] ℝ) (z : I n → ℝ) :=
    (L ∘ V ∘ signedLayerCoordinates.symm) (zface z) *
      (chartVolume D.field (zface z) * coordDeriv 0
        (L ∘ V ∘ signedLayerCoordinates.symm) (zface z))
  have hG (L : ℂ →L[ℝ] ℝ) : Gpair[g,μ,nativeWaveComponent D V L] = -∫ z in Q, read L z :=
    boundaryTrialGreen_eq_flux D μ hμ hlr hl0 hO hOD hBox
      (L.contDiff.comp (hV.comp signedLayerCoordinates.symm.contDiff))
      (waveComponent_compactSupport hVC L)
      (waveComponent_support_halfBox hU B hK.isClosed hKbox a ha ha0 η hTop N h L)
  have hMap : MapsTo zface Q D.ambient := hFace.comp hQU
  have hCont (L : ℂ →L[ℝ] ℝ) : ContinuousOn (read L) Q := by
    have hF := L.contDiff.comp (hV.comp signedLayerCoordinates.symm.contDiff)
    have hz := continuous_normalFacePoint.comp (PiLp.continuous_toLp 2 (fun _ : I n => ℝ))
    have hVol := (CalderonN.contDiffOn_metric_volume D.smooth_field).continuousOn.comp
      hz.continuousOn hMap
    have hD : ContinuousOn (fun z => coordDeriv 0
        (L ∘ V ∘ signedLayerCoordinates.symm) (zface z)) Q :=
      (CalderonN.contDiffOn_coordDeriv hF.contDiffOn isOpen_univ 0).continuousOn.comp
        hz.continuousOn (mapsTo_univ _ _)
    exact (hF.continuous.comp hz).continuousOn.mul (hVol.mul hD)
  have hIntegrable (L : ℂ →L[ℝ] ℝ) : IntegrableOn (read L) Q volume :=
    (hCont L).integrableOn_compact isCompact_Icc
  have hCoef (j : ℕ) : IntegrableOn (fun z : I n → ℝ =>
      faceEnergyCoefficient D.field B a j (WithLp.toLp 2 z)) Q volume := by
    exact ((continuousOn_faceEnergyCoefficient hU D.smooth_field hFace B hK.isClosed a ha ha0 j).comp
      (PiLp.continuous_toLp 2 (fun _ : I n => ℝ)).continuousOn hQU).integrableOn_compact isCompact_Icc
  change h * (Gpair[g,μ,nativeWaveComponent D V Complex.reCLM] +
      Gpair[g,μ,nativeWaveComponent D V Complex.imCLM]) = _
  rw [hG,hG,← neg_add,← integral_add (hIntegrable _) (hIntegrable _),mul_neg,
    ← integral_const_mul,← integral_neg]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun j _ => (hCoef j).const_mul (h ^ j))]
  apply setIntegral_congr_fun measurableSet_Icc
  intro z hz
  let y : Y := WithLp.toLp 2 z
  let E := chartVolume D.field (normalFacePoint y)
  have hz0 : signedLayerCoordinates.symm (zface z) = (y,0) := by
    change signedLayerCoordinates.symm (normalFacePoint y) = _
    rw [← signedLayerCoordinates_face,signedLayerCoordinates.symm_apply_apply]
  have he (L : ℂ →L[ℝ] ℝ) :
      read L z = L (V (y,0)) * (E * L (deriv (fun t => V (y,t)) 0)) := by
    simp only [read,Function.comp_apply,hz0,E]
    rw [coordDeriv_wave_face hV L]
  simp only [he,faceEnergyCoefficient]
  change -(h * ((V (y,0)).re * (E * (deriv (fun t => V (y,t)) 0).re) +
      (V (y,0)).im * (E * (deriv (fun t => V (y,t)) 0).im))) = _
  calc
    _ = -E * (h * ((V (y,0)).re * (deriv (fun t => V (y,t)) 0).re +
        (V (y,0)).im * (deriv (fun t => V (y,t)) 0).im)) := by ring
    _ = _ := by
      rw [B.finiteWave_face_normalPairing a η N hh y,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [E]
      ring

end CalderonPatch.BoundaryLayer
