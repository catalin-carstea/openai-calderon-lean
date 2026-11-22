module

public import Proof.CalderonN.FirstMetricNormalDensity
public import Proof.CalderonN.NormalGeodesicBounds

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped ContDiff Topology Matrix.Norms.Operator

namespace CalderonN

variable {n : ℕ} [NeZero n]

local instance matrixCurveTopology : TopologicalSpace (Mat n) :=
  @NormedAddCommGroup.toMetricSpace (Mat n) Matrix.linftyOpNormedAddCommGroup
    |>.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The coefficient of the affine, scalar first radius variation, normalized
    by the actual positive divergence density at the center. -/
def firstDensityCenterLinear (d : Data n) (y : X n) : X n →L[ℝ] ℝ :=
  (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ •
    (fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) y).comp (frameVectorLinear d.frame y)

def normalizedFirstNormalCoeff (d : Data n) (y : X n) (s : ℝ) (z : X n) (i j : I n) : ℝ :=
  divergenceCoeff (framedNormalMetric d.g₁ d.frame d.expMap y s) z i j /
    firstMetricDensityFactor d.γ d.g₁ y

private theorem NormalCoordinates.framedReferenceMatrix_first_zero
    {Y Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField n} (hg : Elliptic Ω K g)
    (hK : 0 < K) {E : X n × X n → X n} {R : X n → ℝ}
    (hN : NormalCoordinates Y Ω g E R) {y : X n} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : Frame n) (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (z : X n) :
    HasDerivAt (fun s : ℝ => framedNormalMetric g e E y s z) 0 0 := by
  classical
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (hN.framedNormalMetric_first_zero hΩ hg hK hy hyΩ e he z i j).smul_const
        (Matrix.single i j (1 : ℝ) : Mat n)
  have hf : (fun s : ℝ => ∑ i, ∑ j, framedNormalMetric g e E y s z i j •
      (Matrix.single i j (1 : ℝ) : Mat n)) =
      fun s => framedNormalMetric g e E y s z := by
    funext s
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.sum_sum_single (framedNormalMetric g e E y s z)
  simpa only [hf, zero_smul, Finset.sum_const_zero] using h

private theorem NormalCoordinates.framedReferenceCoeff_first_zero
    {Y Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField n} (hg : Elliptic Ω K g)
    (hK : 0 < K) {E : X n × X n → X n} {R : X n → ℝ}
    (hN : NormalCoordinates Y Ω g E R) {y : X n} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : Frame n) (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (z : X n) (i j : I n) :
    HasDerivAt (fun s : ℝ => divergenceCoeff (framedNormalMetric g e E y s) z i j) 0 0 := by
  let A (s : ℝ) := framedNormalMetric g e E y s z
  have hA : HasDerivAt A 0 0 := hN.framedReferenceMatrix_first_zero hΩ hg hK hy hyΩ e he z
  have hA₀ : A 0 = 1 := hN.framedNormalMetric_zero hy e he z
  have hJ : IsUnit (A 0).det := by rw [hA₀, Matrix.det_one]; exact isUnit_one
  have hD : HasDerivAt (fun s => (A s).det) 0 0 := by
    have h := (hasFDerivAt_det_of_isUnit (A 0) hJ).comp_hasDerivAt 0 hA
    exact h.congr_deriv (map_zero (determinantDerivative (A 0)))
  have hId : IsUnit (A 0) := (Matrix.isUnit_iff_isUnit_det _).mpr hJ
  have hB : HasDerivAt (fun s => (A s)⁻¹) 0 0 := by
    have h := (hasFDerivAt_inverseMatrix_of_isUnit (A 0) hId).comp_hasDerivAt 0 hA
    exact h.congr_deriv (map_zero (inverseMatrixDerivative (A 0)))
  let L : Mat n →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hInv : HasDerivAt (fun s => (A s)⁻¹ i j) 0 0 :=
    (L.hasFDerivAt.comp_hasDerivAt 0 hB).congr_deriv (map_zero L)
  have hDet₀ : 0 < (A 0).det := by simp [hA₀]
  have hVolume := hD.sqrt hDet₀.ne'
  have h := hVolume.mul hInv
  change HasDerivAt (fun s => Real.sqrt (A s).det * (A s)⁻¹ i j) _ 0 at h
  change HasDerivAt (fun s => Real.sqrt (A s).det * (A s)⁻¹ i j) 0 0
  exact h.congr_deriv (by simp only [zero_div, zero_mul, mul_zero, add_zero])

/-- The true first-metric divergence coefficient is scalar at the rescaled
    center, for every signed radius. -/
theorem normalizedFirstNormalCoeff_center_of_frame (hn : 2 ≤ n)
    {Y Ω : Set (X n)} {m : ℕ} {K : ℝ} {R : X n → ℝ}
    {M : Fin (m+1) → ℝ} {d : Data n} {e : Frame n}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ e)
    (hN : NormalCoordinates Y Ω d.γ d.expMap R) (hK : 0 < K)
    {y : X n} (hy : y ∈ Y)
    (he : ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0) (s : ℝ) (i j : I n) :
    normalizedFirstNormalCoeff d y s 0 i j = (1 : Mat n) i j := by
  have hyΩ := hN.center_mem hy
  have hzero : frameVector d.frame y (0 : X n) = 0 := by
    rw [← frameVectorLinear_apply, map_zero]
  have hx : d.expMap (y,s • frameVector d.frame y 0) ∈ Ω := by
    simpa only [hzero,smul_zero,hN.exp_zero hy] using hyΩ
  have hA : framedNormalMetric d.γ d.frame d.expMap y s 0 =
      framedNormalMetric d.γ d.frame d.expMap y 0 0 := by
    ext a b
    simp only [framedNormalMetric, hzero, normalPullbackMetricPair, smul_zero]
  rw [hN.framedNormalMetric_zero hy d.frame he] at hA
  unfold normalizedFirstNormalCoeff
  rw [hB.framed_firstMetric_density_coefficient hn hK hx (by simp [hA]),
    show framedFirstDensityFactor d y s 0 = firstMetricDensityFactor d.γ d.g₁ y by
      simp only [framedFirstDensityFactor,hzero,smul_zero,hN.exp_zero hy]]
  rw [mul_comm, mul_div_cancel_right₀ _ (firstMetricDensityFactor_pos _ _ _).ne']
  simp [divergenceCoeff, chartVolume, hA]

/-- The first variation of the normalized first-metric divergence coefficient
    is the affine scalar density variation. The reference metric part vanishes. -/
theorem normalizedFirstNormalCoeff_first_of_frame (hn : 2 ≤ n)
    {Y Ω : Set (X n)} (hΩ : IsOpen Ω) {m : ℕ} {K : ℝ} {R : X n → ℝ}
    {M : Fin (m+1) → ℝ} {d : Data n} {e : Frame n}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ e)
    (hN : NormalCoordinates Y Ω d.γ d.expMap R) (hK : 0 < K)
    {y : X n} (hy : y ∈ Y)
    (he : ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0) (z : X n) (i j : I n) :
    HasDerivAt (fun s : ℝ => normalizedFirstNormalCoeff d y s z i j)
      (firstDensityCenterLinear d y z * (1 : Mat n) i j) 0 := by
  let v := frameVector d.frame y z
  let E (s : ℝ) := d.expMap (y,s • v)
  let A (s : ℝ) := framedNormalMetric d.γ d.frame d.expMap y s z
  let q := firstMetricDensityFactor d.γ d.g₁
  have hyΩ := hN.center_mem hy
  have hE₀ : E 0 = y := by simp only [E, zero_smul, hN.exp_zero hy]
  have hE : HasDerivAt E v 0 := by
    have hIn : HasDerivAt (fun s : ℝ => (y,s • v)) (0,v) 0 := by
      simpa only [id_eq,one_smul] using (hasDerivAt_const (0:ℝ) y).prodMk
        ((hasDerivAt_id (0:ℝ)).smul_const v)
    have h := (hN.differentiableAt_zero hy).hasFDerivAt
    have h' : HasFDerivAt d.expMap (fderiv ℝ d.expMap (y,0)) (y,(0:ℝ) • v) := by
      simpa only [zero_smul] using h
    simpa only [E,Function.comp_def,hN.vertical_zero hy d.frame he v] using h'.comp_hasDerivAt 0 hIn
  have hΩnear : ∀ᶠ s in 𝓝 (0:ℝ), E s ∈ Ω :=
    hE.continuousAt.eventually (hΩ.mem_nhds (hE₀ ▸ hyΩ))
  have hdens : HasDerivAt (fun s => q (E s)) (fderiv ℝ q y v) 0 := by
    have hq := ((hB.firstMetricDensityFactor_smooth hK).contDiffAt (hΩ.mem_nhds hyΩ)).differentiableAt (by simp)
    have hq' : HasFDerivAt q (fderiv ℝ q y) (E 0) := hE₀ ▸ hq.hasFDerivAt
    exact hq'.comp_hasDerivAt 0 hE
  have hA : HasDerivAt A 0 0 :=
    hN.framedReferenceMatrix_first_zero hΩ hB.1 hK hy hyΩ d.frame he z
  have hA₀ : A 0 = 1 := hN.framedNormalMetric_zero hy d.frame he z
  have hdet := (hasFDerivAt_det_of_isUnit (A 0) (by simp [hA₀])).comp_hasDerivAt 0 hA
  have hdetNear : ∀ᶠ s in 𝓝 (0:ℝ), IsUnit (A s).det :=
    (hdet.continuousAt.eventually_ne (by simp [hA₀])).mono fun _ hs => isUnit_iff_ne_zero.mpr hs
  have hRef := hN.framedReferenceCoeff_first_zero hΩ hB.1 hK hy hyΩ d.frame he z i j
  have hRef₀ : divergenceCoeff (framedNormalMetric d.γ d.frame d.expMap y 0) z i j = (1 : Mat n) i j := by
    change Real.sqrt (A 0).det * (A 0)⁻¹ i j = _
    simp [hA₀]
  have hEq :
      (fun s : ℝ => normalizedFirstNormalCoeff d y s z i j) =ᶠ[𝓝 (0:ℝ)]
        fun s => q (E s) * divergenceCoeff (framedNormalMetric d.γ d.frame d.expMap y s) z i j / q y := by
    filter_upwards [hΩnear,hdetNear] with s hs hsJ
    exact congrArg (fun a : ℝ => a / q y) (hB.framed_firstMetric_density_coefficient hn hK hs hsJ i j)
  have h := ((hdens.mul hRef).div_const (q y)).congr_of_eventuallyEq hEq
  simp only [hE₀,hRef₀,zero_mul,mul_zero,zero_add,add_zero] at h
  convert h using 1
  simp only [firstDensityCenterLinear,smul_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,
    frameVectorLinear_apply,v,q,div_eq_mul_inv]
  ring

theorem Admissible.normalizedFirstNormalCoeff_center (hn : 2 ≤ n)
    {Y Ω : Set (X n)} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data n}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X n} (hy : y ∈ Y) (s : ℝ) (i j : I n) :
    normalizedFirstNormalCoeff d y s 0 i j = (1 : Mat n) i j :=
  normalizedFirstNormalCoeff_center_of_frame hn hd.1 hd.2.1 hK hy
    (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)) s i j

theorem Admissible.normalizedFirstNormalCoeff_first (hn : 2 ≤ n)
    {Y Ω : Set (X n)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data n}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X n} (hy : y ∈ Y) (z : X n) (i j : I n) :
    HasDerivAt (fun s : ℝ => normalizedFirstNormalCoeff d y s z i j)
      (firstDensityCenterLinear d y z * (1 : Mat n) i j) 0 :=
  normalizedFirstNormalCoeff_first_of_frame hn hΩ hd.1 hd.2.1 hK hy
    (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)) z i j

end CalderonN
