module

public import Proof.CalderonN.FirstMetricNormalJets
public import Proof.CalderonN.FramedNormalRadialCoefficient

import Proof.CalderonN.ChartBilinear
import Mathlib.Tactic

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace CalderonN

variable {n : ℕ} [NeZero n]

/-- The radial scalar of the normalized first-metric divergence coefficient
in the same normal chart as the Dirichlet response. -/
def firstNormalRadialWeight (d : Data n) (y : X n) (s : ℝ) (z : X n) : ℝ :=
  (framedFirstDensityFactor d y s z / firstMetricDensityFactor d.γ d.g₁ y) *
    Real.sqrt (framedNormalMetric d.γ d.frame d.expMap y s z).det

theorem firstNormalRadialWeight_pos (d : Data n) (y : X n) (s : ℝ) (z : X n)
    (hDet : 0 < (framedNormalMetric d.γ d.frame d.expMap y s z).det) :
    0 < firstNormalRadialWeight d y s z := by
  unfold firstNormalRadialWeight framedFirstDensityFactor
  exact mul_pos (div_pos (firstMetricDensityFactor_pos _ _ _) (firstMetricDensityFactor_pos _ _ _))
    (Real.sqrt_pos.mpr hDet)

/-- Gauss' lemma removes the tangential coefficient for the actual first
metric pulled back to a reference normal sphere. -/
theorem normalizedFirstNormalCoeff_radial_row_of_frame (hn : 2 ≤ n)
    {Y Ω : Set (X n)} (hΩ : IsOpen Ω) {m : ℕ} {K : ℝ} {R : X n → ℝ}
    {M : Fin (m+1) → ℝ} {d : Data n} {e : Frame n}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ e)
    (hN : NormalCoordinates Y Ω d.γ d.expMap R) (hK : 0 < K)
    {y : X n} (hy : y ∈ Y)
    (hFrame : ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    {s : ℝ} (hs : s ≠ 0) (z : X n)
    (hv : s • frameVector d.frame y z ∈ interior (disk d.γ y (R y)))
    (hDet : IsUnit (framedNormalMetric d.γ d.frame d.expMap y s z).det) (j : I n) :
    ∑ i, z i * normalizedFirstNormalCoeff d y s z i j =
      firstNormalRadialWeight d y s z * z j := by
  have hyΩ := hN.center_mem hy
  have hx := hN.path_image hy (s • frameVector d.frame y z) (interior_subset hv)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  rw [one_smul] at hx
  have hFactor := hB.framed_firstMetric_density_coefficient hn hK hx hDet
  have hRad := hN.framedNormal_divergence_radial_row hΩ hB.1 hK hy hyΩ
    d.frame hFrame s hs z hv hDet j
  let b := framedFirstDensityFactor d y s z / firstMetricDensityFactor d.γ d.g₁ y
  calc
    _ = b * (∑ i, z i * divergenceCoeff (framedNormalMetric d.γ d.frame d.expMap y s) z i j) := by
      simp only [normalizedFirstNormalCoeff, hFactor, Finset.mul_sum, b, div_eq_mul_inv]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by rw [hRad, firstNormalRadialWeight]; exact (mul_assoc b _ _).symm

theorem Admissible.normalizedFirstNormalCoeff_radial_row (hn : 2 ≤ n)
    {Y Ω : Set (X n)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data n}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X n} (hy : y ∈ Y) {s : ℝ} (hs : s ≠ 0) (z : X n)
    (hv : s • frameVector d.frame y z ∈ interior (disk d.γ y (max ρ (d.radius y))))
    (hDet : IsUnit (framedNormalMetric d.γ d.frame d.expMap y s z).det) (j : I n) :
    ∑ i, z i * normalizedFirstNormalCoeff d y s z i j =
      firstNormalRadialWeight d y s z * z j :=
  normalizedFirstNormalCoeff_radial_row_of_frame hn hΩ hd.1 hd.2.1 hK hy
    (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)) hs z hv hDet j

/-- The normalized conormal trace is the directional radial derivative
times its actual strictly positive boundary weight. -/
theorem Admissible.normalizedFirstNormalCoeff_conormal (hn : 2 ≤ n)
    {Y Ω : Set (X n)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data n}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X n} (hy : y ∈ Y) {s : ℝ} (hs : s ≠ 0) (z : X n)
    (hv : s • frameVector d.frame y z ∈ interior (disk d.γ y (max ρ (d.radius y))))
    (hDet : IsUnit (framedNormalMetric d.γ d.frame d.expMap y s z).det) (u : X n → ℝ) :
    ∑ i, z i * (∑ j, normalizedFirstNormalCoeff d y s z i j * coordDeriv j u z) =
      firstNormalRadialWeight d y s z * fderiv ℝ u z z := by
  have hDu : fderiv ℝ u z z = ∑ j, coordDeriv j u z * z j :=
    covector_axis_sum (fderiv ℝ u z) z
  rw [hDu]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [hd.normalizedFirstNormalCoeff_radial_row hn hΩ hK hy hs z hv hDet j]
  ring

end CalderonN
