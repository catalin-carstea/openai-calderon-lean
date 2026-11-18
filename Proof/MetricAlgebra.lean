import Proof.Geometry
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace ShrinkingSpheres

lemma metricPair_smul_left (g : MetricField) (y u v : X) (a : ℝ) :
    metricPair g y (a • u) v = a * metricPair g y u v := by
  simp only [metricPair, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_smul_right (g : MetricField) (y u v : X) (a : ℝ) :
    metricPair g y u (a • v) = a * metricPair g y u v := by
  simp only [metricPair, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_sum_left {α : Type*} (s : Finset α) (g : MetricField) (y v : X) (u : α → X) :
    metricPair g y (∑ a ∈ s, u a) v = ∑ a ∈ s, metricPair g y (u a) v := by
  simp only [metricPair, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

lemma metricPair_sum_right {α : Type*} (s : Finset α) (g : MetricField) (y u : X) (v : α → X) :
    metricPair g y u (∑ a ∈ s, v a) = ∑ a ∈ s, metricPair g y u (v a) := by
  simp only [metricPair, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Reconstruction of a tangent vector from coordinates in the chosen orthonormal frame. -/
def frameVector (e : Frame) (y : X) (w : X) : X := ∑ i, w i • e y i

lemma metricPair_frame_expansion (g : MetricField) (e : Frame) (y u v : X) :
    metricPair g y (frameVector e y u) (frameVector e y v) =
      ∑ i, ∑ j, metricPair g y (e y i) (e y j) * u i * v j := by
  unfold frameVector
  rw [metricPair_sum_left]
  simp_rw [metricPair_smul_left, metricPair_sum_right, metricPair_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_frameVector (γ : MetricField) (e : Frame) (y u v : X)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) :
    metricPair γ y (frameVector e y u) (frameVector e y v) = ∑ i, u i * v i := by
  unfold frameVector
  rw [metricPair_sum_left]
  simp_rw [metricPair_smul_left, metricPair_sum_right, metricPair_smul_right, he]
  simp

lemma frameVector_mem_sphere (γ : MetricField) (e : Frame) (y : X)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (w : ↥standardSphere) : frameVector e y w ∈ sphereAt γ y := by
  change metricPair γ y (frameVector e y w) (frameVector e y w) = 1
  rw [metricPair_frameVector γ e y w w he]
  have hw : ‖w.val‖ = 1 := by simpa only [standardSphere, Metric.mem_sphere, dist_zero_right] using w.property
  simpa only [← pow_two, ← EuclideanSpace.real_norm_sq_eq, hw, one_pow]

end ShrinkingSpheres
