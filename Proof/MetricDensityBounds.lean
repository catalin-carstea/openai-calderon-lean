import Proof.InverseMetricEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Matrix
namespace ShrinkingSpheres

lemma Elliptic.entry_abs_bound {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (i j : I) : |g x i j| ≤ K := by
  have hh := hg.metricPair_abs_le hK hx (axis i) (axis j)
  rw [norm_axis,norm_axis,mul_one,mul_one] at hh
  simpa [metricPair,axis] using hh

lemma abs_det_le_six_cube (A : Mat) (K : ℝ) (hK : 0 ≤ K) (hA : ∀ i j,|A i j| ≤ K) :
    |A.det| ≤ 6*K^3 := by
  have hterm (i j k l a b : I) : |A i j*A k l*A a b| ≤ K^3 := by
    simp only [abs_mul]
    have hh := mul_le_mul (mul_le_mul (hA i j) (hA k l) (abs_nonneg _) hK)
      (hA a b) (abs_nonneg _) (mul_nonneg hK hK)
    convert hh using 1 <;> ring
  have hAbs (a b c d e f : ℝ) : |a-b-c+d+e-f| ≤ |a|+|b|+|c|+|d|+|e|+|f| := by
    have h1 := abs_sub a b
    have h2 := abs_sub (a-b) c
    have h3 := abs_add_le (a-b-c) d
    have h4 := abs_add_le (a-b-c+d) e
    have h5 := abs_sub (a-b-c+d+e) f
    linarith only [h1,h2,h3,h4,h5]
  rw [Matrix.det_fin_three]
  have hh := hAbs (A 0 0*A 1 1*A 2 2) (A 0 0*A 1 2*A 2 1) (A 0 1*A 1 0*A 2 2)
    (A 0 1*A 1 2*A 2 0) (A 0 2*A 1 0*A 2 1) (A 0 2*A 1 1*A 2 0)
  linarith only [hh,hterm 0 0 1 1 2 2,hterm 0 0 1 2 2 1,hterm 0 1 1 0 2 2,
    hterm 0 1 1 2 2 0,hterm 0 2 1 0 2 1,hterm 0 2 1 1 2 0]

def metricDensityBudget (K : ℝ) : ℝ := 6*K^3+1

lemma metricDensity_inverse (g : MetricField) (x : X) :
    metricDensity (fun y => (g y)⁻¹) x = (metricDensity g x)⁻¹ := by
  simp only [metricDensity,Matrix.det_nonsing_inv,Ring.inverse_eq_inv',Real.sqrt_inv]

lemma Elliptic.density_upper_bound {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    metricDensity g x ≤ metricDensityBudget K := by
  have hDet := (le_abs_self ((g x).det)).trans
    (abs_det_le_six_cube (g x) K hK.le (fun i j => hg.entry_abs_bound hK hx i j))
  have hB : 0 ≤ metricDensityBudget K := by unfold metricDensityBudget; positivity
  have hSq : 6*K^3 ≤ (metricDensityBudget K)^2 := by
    unfold metricDensityBudget
    nlinarith [sq_nonneg (6*K^3),show 0 ≤ 6*K^3 by positivity]
  exact Real.sqrt_le_iff.mpr ⟨hB,hDet.trans hSq⟩

/-- Explicit uniform upper and lower volume density bounds from ellipticity alone. -/
theorem Elliptic.density_bounds {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    (metricDensityBudget K)⁻¹ ≤ metricDensity g x ∧ metricDensity g x ≤ metricDensityBudget K := by
  refine ⟨?_,hg.density_upper_bound hK hx⟩
  have hInv := (hg.inverse_metric hK).density_upper_bound hK hx
  rw [metricDensity_inverse] at hInv
  have hρ : 0 < metricDensity g x := Real.sqrt_pos.mpr (hg.posDef hK hx).det_pos
  have hB : 0 < metricDensityBudget K := by unfold metricDensityBudget; positivity
  have hh := mul_le_mul_of_nonneg_right hInv hρ.le
  rw [inv_mul_cancel₀ hρ.ne'] at hh
  have hMult := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hB.le)
  simpa only [mul_one,← mul_assoc,inv_mul_cancel₀ hB.ne',one_mul] using hMult

end ShrinkingSpheres
