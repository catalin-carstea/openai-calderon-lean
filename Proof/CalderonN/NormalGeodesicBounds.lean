module

public import Proof.CalderonN.NormalGeodesicPath

import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma NormalCoordinates.center_mem {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y) : y ∈ Ω := by
  have hz := ((hN.2 y hy).2.2 0 (zero_mem_disk g y (R y))).1
  simpa only [hN.exp_zero hy] using hz

/-- Uniform coordinate speed bound, before replacing the initial metric speed by
    its ellipticity bound. It holds throughout the admitted normal geodesic. -/
theorem NormalCoordinates.geodesic_speed_sq {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun s : ℝ => expMap (y,s • v)) t‖^2 ≤ K*metricPair g y v v := by
  have hl := ((hg.2 _ (hN.path_image hy v hv ht)).2 (deriv (fun s : ℝ => expMap (y,s • v)) t)).1
  rw [hN.geodesic_energy_constant hΩ hg hK hy v hv ht] at hl
  have hh := mul_le_mul_of_nonneg_left hl hK.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] using hh

/-- Ellipticity alone controls the speed uniformly in the admitted configuration. -/
theorem NormalCoordinates.geodesic_speed_le {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun s : ℝ => expMap (y,s • v)) t‖ ≤ K*‖v‖ := by
  have hh := (hN.geodesic_speed_sq hΩ hg hK hy v hv ht).trans
    (mul_le_mul_of_nonneg_left ((hg.2 y (hN.center_mem hy)).2 v).2 hK.le)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK.le (norm_nonneg _))).mp
  convert hh using 1 <;> ring

/-- Uniform displacement of every actual normal geodesic. In particular all small
    rescaled balls stay quantitatively close to their centers. -/
theorem NormalCoordinates.geodesic_displacement_le {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖expMap (y,t • v)-y‖ ≤ K*t*‖v‖ := by
  obtain ⟨U,hU,hI,hReg⟩ := hN.smoothNear_path hy v hv
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le (C:=K*‖v‖)
    (fun s hs => (hReg.contDiffAt (hU.mem_nhds (hI hs))).differentiableAt (by simp))
    (fun s hs => hN.geodesic_speed_le hΩ hg hK hy v hv hs) hzero ht
  have hb' : ‖expMap (y,t • v)-y‖ ≤ (K*‖v‖)*t := by
    simpa only [zero_smul,hN.exp_zero hy,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using hb
  nlinarith only [hb']

end CalderonN
