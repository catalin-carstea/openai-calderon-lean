module

public import Proof.CalderonPatch.MeasuredWaveAsymptotic

import Proof.CalderonPatch.PairedBoundaryTrials
import Proof.CalderonPatch.FiniteAsymptoticCoefficients
import Mathlib.Tactic

public section
noncomputable section
open Filter Finset MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "Y" => X n
local notation "Z" => X (n+1)
local notation "J" => 𝓡∂ (n+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "H" => inwardHalfSpace (n+1)

omit [T2Space M] [CompactSpace M] [BorelSpace M] [PreconnectedSpace M] in
private theorem dirichletQuadraticEnergy_congr_trace
    (g : SmoothMetric (n+1) M) (μ : Measure M) {f k : M → ℝ}
    (h : EqOn f k ((J).boundary M)) :
    dirichletQuadraticEnergy g μ f = dirichletQuadraticEnergy g μ k := by
  unfold dirichletQuadraticEnergy
  congr 1
  ext c
  exact ⟨fun ⟨u,hu,huf,he⟩ => ⟨u,hu,huf.trans h,he⟩,
    fun ⟨u,hu,huk,he⟩ => ⟨u,hu,huk.trans h.symm,he⟩⟩

variable {d₁ d₂ : DirichletData n M} {p₁ p₂ : M}
  (D₁ : NativeBoundaryMetricChart d₁.metric p₁) (D₂ : NativeBoundaryMetricChart d₂.metric p₂)

/-- The two finite waves have the same supported trace for each real
component, regardless of their different interior profiles. -/
theorem measuredWaveEnergy_eq_of_patchEnergy
    {Γ : Set ((J).boundary M)} (hMeas : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {l r : I (n+1) → ℝ} (hl0 : l 0 = 0)
    {O : Set Z} (hOD₁ : O ⊆ D₁.ambient) (hOD₂ : O ⊆ D₂.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) O)
    (hSame : EqOn D₁.coord.symm D₂.coord.symm (O ∩ {z | z 0 = 0}))
    (hΓ : MapsTo (D₁.coord.symm ∘ normalFacePoint) (tangentialBox l r) (Subtype.val '' Γ))
    {U : Set Y} (hU : IsOpen U) {ξ : I n → ℝ}
    (B₁ B₂ : BoundaryLayerCoefficients ξ U)
    {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U) (hKbox : K ⊆ tangentialBox l r)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ)) (hTop : η.rOut < r 0) (N : ℕ) (h : ℝ) :
    measuredWaveEnergy d₁ D₁ (B₁.finiteWave a η N h) =
      measuredWaveEnergy d₂ D₂ (B₂.finiteWave a η N h) := by
  let V₁ := B₁.finiteWave a η N h
  let V₂ := B₂.finiteWave a η N h
  have hη : η 0 = 1 := η.one_of_mem_closedBall (Metric.mem_closedBall_self η.rIn_pos.le)
  have hV (B : BoundaryLayerCoefficients ξ U) :=
    B.finiteWave_contDiff hU hK.isClosed hKU a ha ha0 η η.contDiff N h
  have hVc (B : BoundaryLayerCoefficients ξ U) :=
    B.finiteWave_hasCompactSupport hU hK a ha ha0 η η.hasCompactSupport N h
  have hS (B : BoundaryLayerCoefficients ξ U) (L : ℂ →L[ℝ] ℝ) :=
    waveComponent_support_halfBox hU B hK.isClosed hKbox a ha ha0 η hTop N h L
  have hC (B : BoundaryLayerCoefficients ξ U) (L : ℂ →L[ℝ] ℝ) :
      tsupport (L ∘ B.finiteWave a η N h ∘ signedLayerCoordinates.symm) ∩ H ⊆ O := by
    intro z hz
    have hBox' := hBox (normalHalfBox_subset_closedBox hl0 (hS B L hz))
    change WithLp.toLp 2 (WithLp.ofLp z) ∈ O at hBox'
    simpa only [WithLp.toLp_ofLp] using hBox'
  have hComp (L : ℂ →L[ℝ] ℝ) :
      dirichletQuadraticEnergy d₁.metric d₁.volume (nativeWaveComponent D₁ V₁ L) =
        dirichletQuadraticEnergy d₂.metric d₂.volume (nativeWaveComponent D₂ V₂ L) := by
    let f₁ := L ∘ V₁ ∘ signedLayerCoordinates.symm
    let f₂ := L ∘ V₂ ∘ signedLayerCoordinates.symm
    have hf₁c : HasCompactSupport f₁ := waveComponent_compactSupport (hVc B₁) L
    have hf₂c : HasCompactSupport f₂ := waveComponent_compactSupport (hVc B₂) L
    have hT₁ : tsupport f₁ ∩ H ⊆ D₁.coord.target := by
      rw [D₁.target_eq]
      exact fun z hz => ⟨hOD₁ (hC B₁ L hz),hz.2⟩
    have hu₁ : ContMDiff J R ∞ (nativeWaveComponent D₁ V₁ L) :=
      contMDiff_boundaryChartTest D₁
        (L.contDiff.comp ((hV B₁).comp signedLayerCoordinates.symm.contDiff)) hf₁c hT₁
    have hTrace : EqOn (nativeWaveComponent D₁ V₁ L) (nativeWaveComponent D₂ V₂ L) ((J).boundary M) := by
      apply eqOn_boundaryChartTests_of_common_face D₁ D₂ hOD₁ hOD₂ hf₁c hf₂c
        (hC B₁ L) (hC B₂ L) hSame
      intro z hz
      let w := signedLayerCoordinates.symm z
      have hw : w.2 = 0 := by
        rw [← signedLayerCoordinates_height w,show signedLayerCoordinates w = z from
          signedLayerCoordinates.apply_symm_apply z]
        exact hz.2
      have he : w = (w.1,0) := Prod.ext rfl hw
      change L (V₁ w) = L (V₂ w)
      rw [he]
      dsimp only [V₁,V₂]
      rw [B₁.finiteWave_face a η hη,B₂.finiteWave_face a η hη]
    have hSupport : tsupport (fun x : (J).boundary M => nativeWaveComponent D₁ V₁ L x) ⊆ Γ :=
      tsupport_boundaryChartTest_trace_subset D₁ hl0 (hBox.mono_right hOD₁) hf₁c (hS B₁ L) hΓ
    exact (hMeas _ hu₁ hSupport).trans
      (dirichletQuadraticEnergy_congr_trace d₂.metric d₂.volume hTrace)
  unfold measuredWaveEnergy
  rw [hComp Complex.reCLM,hComp Complex.imCLM]

/-- All integrated face coefficients of an arbitrary localized wave
are determined by the measured patch energy. -/
theorem integral_faceEnergyCoefficient_eq_of_patchEnergy
    {Γ : Set ((J).boundary M)} (hMeas : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {l r : I (n+1) → ℝ} (hlr : l ≤ r) (hl0 : l 0 = 0)
    {O : Set Z} (hO : IsOpen O) (hOD₁ : O ⊆ D₁.ambient) (hOD₂ : O ⊆ D₂.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) O)
    (hSame : EqOn D₁.coord.symm D₂.coord.symm (O ∩ {z | z 0 = 0}))
    (hΓ : MapsTo (D₁.coord.symm ∘ normalFacePoint) (tangentialBox l r) (Subtype.val '' Γ))
    {U : Set Y} (hU : IsOpen U)
    (hFace₁ : MapsTo normalFacePoint U D₁.ambient) (hFace₂ : MapsTo normalFacePoint U D₂.ambient)
    (hQU : MapsTo (WithLp.toLp 2) (Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0)) U)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0)
    {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U) (hKbox : K ⊆ tangentialBox l r)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ)) (hTop : η.rOut < r 0) (k : ℕ) :
    let B₁ := boundaryLayerCoefficientsOfMetric D₁.open_ambient D₁.field D₁.smooth_field
      (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₁ hy) ξ hξ
    let B₂ := boundaryLayerCoefficientsOfMetric D₂.open_ambient D₂.field D₂.smooth_field
      (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₂ hy) ξ hξ
    (∫ z in Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0),
      faceEnergyCoefficient D₁.field B₁ a k (WithLp.toLp 2 z)) =
    (∫ z in Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0),
      faceEnergyCoefficient D₂.field B₂ a k (WithLp.toLp 2 z)) := by
  let B₁ := boundaryLayerCoefficientsOfMetric D₁.open_ambient D₁.field D₁.smooth_field
      (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₁ hy) ξ hξ
  let B₂ := boundaryLayerCoefficientsOfMetric D₂.open_ambient D₂.field D₂.smooth_field
      (fun y hy => by simpa only [signedLayerCoordinates_face] using hFace₂ hy) ξ hξ
  let S := Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0)
  let E₁ (j : ℕ) := ∫ z in S, faceEnergyCoefficient D₁.field B₁ a j (WithLp.toLp 2 z)
  let E₂ (j : ℕ) := ∫ z in S, faceEnergyCoefficient D₂.field B₂ a j (WithLp.toLp 2 z)
  let N := k+1
  have hN : 0 < N := Nat.succ_pos k
  obtain ⟨C₁,_,hB₁⟩ := exists_measuredWaveEnergy_remainder d₁ D₁ hlr hl0 hO hOD₁ hBox
    hU hFace₁ hQU ξ hξ hK hKU hKbox a ha ha0 η hTop N hN
  obtain ⟨C₂,_,hB₂⟩ := exists_measuredWaveEnergy_remainder d₂ D₂ hlr hl0 hO hOD₂ hBox
    hU hFace₂ hQU ξ hξ hK hKU hKbox a ha ha0 η hTop N hN
  have hB (h : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) :
      |∑ j ∈ range (N+1), h ^ j * (E₁ j - E₂ j)| ≤ (C₁+C₂) * h ^ N := by
    let T := h * measuredWaveEnergy d₁ D₁ (B₁.finiteWave a η N h)
    have hEq := measuredWaveEnergy_eq_of_patchEnergy D₁ D₂ hMeas hl0 hOD₁ hOD₂ hBox
      hSame hΓ hU B₁ B₂ hK hKU hKbox a ha ha0 η hTop N h
    have h₁ : |T - ∑ j ∈ range (N+1), h ^ j * E₁ j| ≤ C₁ * h ^ N := hB₁ h hh hh₁
    have h₂ : |T - ∑ j ∈ range (N+1), h ^ j * E₂ j| ≤ C₂ * h ^ N := by
      dsimp only [T]
      rw [hEq]
      exact hB₂ h hh hh₁
    simp only [mul_sub,Finset.sum_sub_distrib]
    let A := ∑ j ∈ range (N+1), h ^ j * E₁ j
    let B := ∑ j ∈ range (N+1), h ^ j * E₂ j
    change |A - B| ≤ _
    calc
      _ = |(T - B) + (-(T - A))| := congrArg (abs : ℝ → ℝ) (by ring)
      _ ≤ |T - B| + |-(T - A)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg,add_comm C₁ C₂,add_mul]; exact add_le_add h₂ h₁
  change E₁ k = E₂ k
  exact sub_eq_zero.mp (finite_power_coefficient_eq_zero hB k (Nat.lt_succ_self k))

end CalderonPatch.BoundaryLayer
