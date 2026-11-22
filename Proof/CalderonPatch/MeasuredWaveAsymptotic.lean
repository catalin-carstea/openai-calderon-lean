module

public import Proof.CalderonPatch.BoundaryWaveFlux
public import Proof.CalderonPatch.BoundaryTrialWaveBounds

import Mathlib.Tactic

public section
noncomputable section
open Filter Finset MeasureTheory Set
open scoped ContDiff Manifold ENNReal NNReal

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "Y" => X n
local notation "Z" => X (n+1)
local notation "J" => 𝓡∂ (n+1)
local notation "R" => 𝓘(ℝ,ℝ)

local notation "Q[" d "," f "]" => dirichletQuadraticEnergy (DirichletData.metric d) (DirichletData.volume d) f
local notation "Gpair[" d "," u "]" =>
  (∫ x, u x * nativeLaplace (DirichletData.metric d) u x +
    covectorEnergy (DirichletData.metric d) x (mfderiv J R u x) ∂(DirichletData.volume d))

/-- The variational measurement of the two real components of the wave
with a common complex boundary trace. -/
@[expose] def measuredWaveEnergy (d : DirichletData n M) {p : M}
    (D : NativeBoundaryMetricChart (d).metric p) (V : Y × ℝ → ℂ) : ℝ :=
  Q[d,nativeWaveComponent D V Complex.reCLM] + Q[d,nativeWaveComponent D V Complex.imCLM]

private theorem complex_scaled_component_bounds {h C r s : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (hR : ‖(h : ℂ) ^ 2 * (⟨r,s⟩ : ℂ)‖ ≤ C * h ^ (N+1)) :
    |r| ≤ C * h ^ (N-1) ∧ |s| ≤ C * h ^ (N-1) := by
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh] at hR
  have he : h ^ (N+1) = h ^ 2 * h ^ (N-1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [he,mul_left_comm] at hR
  have hB := le_of_mul_le_mul_left hR (pow_pos hh 2)
  exact ⟨(Complex.abs_re_le_norm _).trans hB, (Complex.abs_im_le_norm _).trans hB⟩

/-- For every finite order, the scaled measured wave energy differs
from its explicit face polynomial by a uniform error of that order. -/
theorem exists_measuredWaveEnergy_remainder (d : DirichletData n M) {p : M}
    (D : NativeBoundaryMetricChart (d).metric p)
    {l r : I (n+1) → ℝ} (hlr : l ≤ r) (hl0 : l 0 = 0)
    {O : Set Z} (hO : IsOpen O) (hOD : O ⊆ D.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) O)
    {U : Set Y} (hU : IsOpen U) (hFace : MapsTo normalFacePoint U D.ambient)
    (hQU : MapsTo (WithLp.toLp 2) (Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0)) U)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0)
    {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U) (hKbox : K ⊆ tangentialBox l r)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ)) (hTop : η.rOut < r 0)
    (N : ℕ) (hN : 0 < N) :
    let hFace' : MapsTo (fun y : Y => signedLayerCoordinates (y,(0 : ℝ))) U D.ambient :=
      fun y hy => by simpa only [signedLayerCoordinates_face] using hFace hy
    let B := boundaryLayerCoefficientsOfMetric D.open_ambient D.field D.smooth_field hFace' ξ hξ
    ∃ C ≥ (0 : ℝ), ∀ h : ℝ, 0 < h → h ≤ 1 →
      |h * measuredWaveEnergy d D (B.finiteWave a η N h) -
        ∑ j ∈ range (N+1), h ^ j * (∫ z in Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0),
          faceEnergyCoefficient D.field B a j (WithLp.toLp 2 z))| ≤ C * h ^ N := by
  let hFace' : MapsTo (fun y : Y => signedLayerCoordinates (y,(0 : ℝ))) U D.ambient :=
    fun y hy => by simpa only [signedLayerCoordinates_face] using hFace hy
  let B := boundaryLayerCoefficientsOfMetric D.open_ambient D.field D.smooth_field hFace' ξ hξ
  have hRect : K ×ˢ Icc 0 η.rOut ⊆ signedLayerCoordinates ⁻¹' D.ambient := by
    intro w hw
    have h := hBox (normalHalfBox_subset_closedBox hl0 (signedLayerCoordinates_mapsTo_halfBox hKbox hTop hw))
    change WithLp.toLp 2 (WithLp.ofLp (signedLayerCoordinates w)) ∈ O at h
    rw [WithLp.toLp_ofLp] at h
    exact hOD h
  obtain ⟨A,hA,hVal⟩ := B.exists_finiteWave_norm_bound hU hK hKU a ha ha0 η N
  obtain ⟨C,hC,hResidual⟩ := exists_native_finiteWave_laplace_bound D hU hFace' ξ hξ
    hK hKU a ha ha0 η hRect N
  let Z₀ : ℝ := (((measureUnivNNReal (d).volume) ^ ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ)
  let S := ‖d.l2Value‖ ^ 2 * (Z₀*C)^2 + ((d).volume univ).toReal * (A*C)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  refine ⟨2*S,by positivity,fun h hh hh₁ => ?_⟩
  let V := B.finiteWave a η N h
  let u := nativeWaveComponent D V Complex.reCLM
  let v := nativeWaveComponent D V Complex.imCLM
  let e := C * h ^ (N-1)
  have he : 0 ≤ e := mul_nonneg hC (pow_nonneg hh.le _)
  obtain ⟨hu,hv,hR⟩ := hResidual h hh hh₁
  have hBoth (x : M) : |nativeLaplace (d).metric u x| ≤ e ∧ |nativeLaplace (d).metric v x| ≤ e := by
    simpa only [abs_neg] using complex_scaled_component_bounds hh hN (hR x)
  have hBu := d.abs_dirichletQuadraticEnergy_sub_green_le hu hA he
    (abs_nativeWaveComponent_le D hA (hVal h hh hh₁) Complex.reCLM Complex.abs_re_le_norm)
    (fun x => (hBoth x).1)
  have hBv := d.abs_dirichletQuadraticEnergy_sub_green_le hv hA he
    (abs_nativeWaveComponent_le D hA (hVal h hh hh₁) Complex.imCLM Complex.abs_im_le_norm)
    (fun x => (hBoth x).2)
  have he' : ‖d.l2Value‖ ^ 2 * (Z₀*e)^2 + ((d).volume univ).toReal * (A*e) ≤
      S * h ^ (N-1) := by
    let w := h ^ (N-1)
    have hw : 0 ≤ w := pow_nonneg hh.le _
    have hw1 : w ≤ 1 := pow_le_one₀ hh.le hh₁
    have hw2 : w ^ 2 ≤ w := by nlinarith only [mul_nonneg hw (sub_nonneg.mpr hw1)]
    calc
      _ = ‖d.l2Value‖ ^ 2 * (Z₀*C)^2 * w^2 + ((d).volume univ).toReal * (A*C) * w := by dsimp [e,w]; ring
      _ ≤ ‖d.l2Value‖ ^ 2 * (Z₀*C)^2 * w + ((d).volume univ).toReal * (A*C) * w :=
        add_le_add (mul_le_mul_of_nonneg_left hw2 (mul_nonneg (sq_nonneg _) (sq_nonneg _))) le_rfl
      _ = _ := by dsimp only [S,w]; ring
  have hP := finiteWave_nativeGreen_polynomial D (d).volume d.metric_volume hlr hl0 hO hOD hBox
    hU hFace hQU B hK hKU hKbox a ha ha0 η hTop N hh.ne'
  change |h * (Q[d,u] + Q[d,v]) - _| ≤ _
  rw [← hP,← mul_sub,abs_mul,abs_of_pos hh]
  have hSub : Q[d,u] + Q[d,v] - (Gpair[d,u] + Gpair[d,v]) =
      (Q[d,u] - Gpair[d,u]) + (Q[d,v] - Gpair[d,v]) := by ring
  rw [hSub]
  calc
    _ ≤ h * (|Q[d,u] - Gpair[d,u]| + |Q[d,v] - Gpair[d,v]|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hh.le
    _ ≤ h * (S * h ^ (N-1) + S * h ^ (N-1)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hBu.trans he') (hBv.trans he')) hh.le
    _ = _ := by
      have hPow : h ^ N = h ^ (N-1) * h := by rw [← pow_succ,Nat.sub_add_cancel hN]
      rw [hPow]
      ring

end CalderonPatch.BoundaryLayer
