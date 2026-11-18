import Proof.NormalDiskInterior

noncomputable section
set_option autoImplicit false
open Set
namespace ShrinkingSpheres

/-- One strict admitted velocity and its unit norm bound control every point
    of its radial segment; shared by tensor and scalar Taylor estimates. -/
lemma Elliptic.strict_normal_segment_bounds {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (v : X) (R : ℝ)
    (hv : metricPair g y v v < R^2) (hv1 : ‖v‖ ≤ 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    metricPair g y (t • v) (t • v) < R^2 ∧ ‖t • v‖ ≤ 1 := by
  have hVal0 : 0 ≤ metricPair g y v v :=
    (show 0 ≤ K⁻¹*‖v‖^2 by positivity).trans (((hg.2 y hy).2 v).1)
  have htSq : t^2 ≤ 1 := by nlinarith only [ht.1,ht.2]
  constructor
  · rw [metricPair_smul_left,metricPair_smul_right]
    exact (show t*(t*metricPair g y v v) ≤ metricPair g y v v by
      nlinarith only [mul_le_mul_of_nonneg_right htSq hVal0]).trans_lt hv
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans hv1

end ShrinkingSpheres
