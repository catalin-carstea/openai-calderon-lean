import Proof.TauEllipticityBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Matrix
namespace ShrinkingSpheres

lemma metricPair_inverseMetricColumn_right {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (j : I) (v : X) :
    metricPair g y (inverseMetricColumn g y j) v = v j := by
  have hm := Matrix.nonsing_inv_mul (g y) (isUnit_iff_ne_zero.mpr (h.posDef hK hy).det_pos.ne')
  have hcol (l : I) : ∑ i,(g y)⁻¹ i j*g y i l = if j = l then 1 else 0 := by
    have hs (i : I) : (g y)⁻¹ i j = (g y)⁻¹ j i := by
      have hinv : ((g y)⁻¹).transpose = (g y)⁻¹ := by rw [Matrix.transpose_nonsing_inv,(h.2 y hy).1]
      exact congrArg (fun A : Mat => A j i) hinv
    simpa only [Matrix.mul_apply,Matrix.one_apply,hs] using congrArg (fun A : Mat => A j l) hm
  have hcol' (l : I) : ∑ i,g y i l*(g y)⁻¹ i j = if j = l then 1 else 0 := by
    simpa only [mul_comm] using hcol l
  change (∑ i,∑ l,g y i l*(g y)⁻¹ i j*v l) = v j
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hcol']
  simp

def inverseMetricVector (g : MetricField) (y u : X) : X := ∑ j,u j • inverseMetricColumn g y j

lemma inverseMetricVector_apply (g : MetricField) (y u : X) (i : I) :
    inverseMetricVector g y u i = ∑ j,u j*(g y)⁻¹ i j := by
  simp only [inverseMetricVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    inverseMetricColumn,WithLp.ofLp_toLp,smul_eq_mul]

lemma metricPair_inverseMetricVector_right {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (u v : X) :
    metricPair g y (inverseMetricVector g y u) v = ∑ j,u j*v j := by
  rw [inverseMetricVector,metricPair_sum_left]
  simp_rw [metricPair_smul_left,metricPair_inverseMetricColumn_right h hK hy]

lemma inverse_metricPair_eq_sum (g : MetricField) (y u v : X) :
    metricPair (fun x => (g x)⁻¹) y u v = ∑ i,u i*inverseMetricVector g y v i := by
  simp only [metricPair,inverseMetricVector_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Inverting a positive definite metric preserves the same quadratic ellipticity
    constants. The proof uses the actual inverse matrix, not an abstract dual metric. -/
theorem Elliptic.inverse_quadratic_bounds {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (u : X) :
    K⁻¹*‖u‖^2 ≤ metricPair (fun x => (g x)⁻¹) y u u ∧
      metricPair (fun x => (g x)⁻¹) y u u ≤ K*‖u‖^2 := by
  let v := inverseMetricVector g y u
  let q := metricPair (fun x => (g x)⁻¹) y u u
  have hq : q = metricPair g y v v := by
    rw [metricPair_inverseMetricVector_right h hK hy]
    exact inverse_metricPair_eq_sum g y u u
  have hdual : metricPair g y v u = ‖u‖^2 := by
    rw [metricPair_inverseMetricVector_right h hK hy]
    simp only [← pow_two,← EuclideanSpace.real_norm_sq_eq]
  have hInner : q = inner ℝ u v := by
    change metricPair (fun x => (g x)⁻¹) y u u = inner ℝ u v
    rw [inverse_metricPair_eq_sum,EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial,dotProduct,v,mul_comm]
  have hqUpper : q ≤ ‖u‖*‖v‖ := by
    rw [hInner]
    exact (le_abs_self _).trans (abs_real_inner_le_norm u v)
  have hLo := ((h.2 y hy).2 v).1
  rw [← hq] at hLo
  have hq0 : 0 ≤ q := (mul_nonneg (inv_nonneg.mpr hK.le) (sq_nonneg ‖v‖)).trans hLo
  have hLo' : ‖v‖^2 ≤ K*q := by
    simpa only [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] using mul_le_mul_of_nonneg_left hLo hK.le
  have hvBound : ‖v‖ ≤ K*‖u‖ := by
    by_cases hv0 : v = 0
    · rw [hv0,norm_zero]
      positivity
    · have hh := mul_le_mul_of_nonneg_left hqUpper hK.le
      have hs : ‖v‖*‖v‖ ≤ (K*‖u‖)*‖v‖ := by nlinarith only [hLo',hh]
      exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv0)).mp hs
  refine ⟨?_,?_⟩
  · by_cases hu : u = 0
    · subst u
      simp [metricPair]
    · have hc := h.metricPair_cauchy_sq hK hy v u
      rw [hdual,← hq] at hc
      have hh := mul_le_mul_of_nonneg_left ((h.2 y hy).2 u).2 hq0
      have hFact : ‖u‖^2*‖u‖^2 ≤ (K*q)*‖u‖^2 := by nlinarith only [hc,hh]
      have hNorm : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
      have hCancel := (mul_le_mul_iff_left₀ hNorm).mp hFact
      have hMul := mul_le_mul_of_nonneg_left hCancel (inv_nonneg.mpr hK.le)
      simpa only [← mul_assoc,inv_mul_cancel₀ hK.ne',one_mul] using hMul
  · have hh := hqUpper.trans (mul_le_mul_of_nonneg_left hvBound (norm_nonneg u))
    nlinarith only [hh]

theorem Elliptic.inverse_metric {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) : Elliptic Ω K (fun x => (g x)⁻¹) := by
  refine ⟨fun i j => h.contDiffOn_inverse_entry hK i j,?_⟩
  intro y hy
  refine ⟨?_,fun u => h.inverse_quadratic_bounds hK hy u⟩
  rw [Matrix.transpose_nonsing_inv,(h.2 y hy).1]

end ShrinkingSpheres
