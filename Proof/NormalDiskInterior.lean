import Proof.UniformNormalInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set
namespace ShrinkingSpheres

/-- At positive radius the interior of the actual quadratic disk has a strict
    quadratic inequality. This uses radial dilation, with no extra metric premise. -/
lemma metricPair_lt_of_mem_interior_disk (g : MetricField) (y v : X) (R : ℝ)
    (hR : 0 < R) (hv : v ∈ interior (disk g y R)) : metricPair g y v v < R^2 := by
  have hDisk : v ∈ disk g y R := interior_subset hv
  have hle : metricPair g y v v ≤ R^2 := hDisk
  by_contra hnot
  have heq : metricPair g y v v = R^2 := le_antisymm hle (le_of_not_gt hnot)
  obtain ⟨δ,hδ,hBall⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hv)
  let s : ℝ := δ/(2*(‖v‖+1))
  have hs : 0 < s := div_pos hδ (by positivity)
  have hsd : s*(2*(‖v‖+1)) = δ := by dsimp only [s];field_simp
  have hDist : dist ((1+s) • v) v < δ := by
    rw [dist_eq_norm]
    have hSub : (1+s) • v-v = s • v := by module
    rw [hSub,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    nlinarith [norm_nonneg v]
  have hOut : (1+s) • v ∈ disk g y R := hBall hDist
  change metricPair g y ((1+s) • v) ((1+s) • v) ≤ R^2 at hOut
  rw [metricPair_smul_left,metricPair_smul_right,heq] at hOut
  have hSq : 0 < R^2 := sq_pos_of_pos hR
  have hS : 1 < (1+s)^2 := by nlinarith [sq_nonneg s]
  have hh := mul_lt_mul_of_pos_right hS hSq
  nlinarith only [hOut,hh]

end ShrinkingSpheres
