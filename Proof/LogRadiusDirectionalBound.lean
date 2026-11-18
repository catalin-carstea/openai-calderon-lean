import Proof.ProfileRadiusJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
namespace ShrinkingSpheres

/-- Coordinate logarithmic-radius control bounds every actual center
    direction, using only the reference ellipticity and orthonormal frame. -/
theorem Elliptic.logRadius_direction_bound {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 1 ≤ K) (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Ω)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (a : X) :
    |fderiv ℝ (fun x => Real.log (r x)) y a| ≤ 3*K*beta g r y*‖a‖ := by
  rw [linear_axis_expansion]
  calc
    _ ≤ ∑ i,|a i*fderiv ℝ (fun x => Real.log (r x)) y (axis i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I,‖a‖*(K*beta g r y) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have ha : |a i| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le a i
      exact mul_le_mul ha (h.coord_logRadius_bound hK e r hy he i) (abs_nonneg _ ) (norm_nonneg a)
    _ = _ := by simp only [Fin.sum_univ_three];ring

end ShrinkingSpheres
