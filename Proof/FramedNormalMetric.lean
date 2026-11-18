import Proof.UniformPullbackEllipticity
import Proof.FramePullback

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace ShrinkingSpheres

/-- Actual rescaled normal metric in the fixed orthonormal frame at its center.
    The square of the radius has been removed from the pullback. -/
def framedNormalMetric (g : MetricField) (e : Frame) (expMap : X × X → X) (y : X) (r : ℝ) : MetricField :=
  fun z i j => normalPullbackMetricPair g expMap y r (frameVector e y z) (e y i) (e y j)

lemma framedNormalMetric_pair (g : MetricField) (e : Frame) (expMap : X × X → X)
    (y z u v : X) (r : ℝ) :
    metricPair (framedNormalMetric g e expMap y r) z u v =
      normalPullbackMetricPair g expMap y r (frameVector e y z) (frameVector e y u) (frameVector e y v) := by
  let L := normalVerticalJacobian expMap y (r • frameVector e y z)
  have hu : L (frameVector e y u) = ∑ i,u i • L (e y i) := by simp only [frameVector,map_sum,map_smul]
  have hv : L (frameVector e y v) = ∑ j,v j • L (e y j) := by simp only [frameVector,map_sum,map_smul]
  change (∑ i,∑ j,framedNormalMetric g e expMap y r z i j*u i*v j) =
    metricPair g (expMap (y,r • frameVector e y z)) (L (frameVector e y u)) (L (frameVector e y v))
  rw [hu,hv,metricPair_sum_left]
  simp_rw [metricPair_smul_left,metricPair_sum_right,metricPair_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change normalPullbackMetricPair g expMap y r (frameVector e y z) (e y i) (e y j)*u i*v j =
    u i*(v j*normalPullbackMetricPair g expMap y r (frameVector e y z) (e y i) (e y j))
  ring

lemma metricPair_frameVector_self (g : MetricField) (e : Frame) (y u : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    metricPair g y (frameVector e y u) (frameVector e y u) = ‖u‖^2 := by
  rw [metricPair_frameVector g e y u u hframe]
  simp only [← pow_two,← EuclideanSpace.real_norm_sq_eq]

lemma Elliptic.frameVector_norm_sq_bounds {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (e : Frame)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (u : X) :
    ‖u‖^2 ≤ K*‖frameVector e y u‖^2 ∧ ‖frameVector e y u‖^2 ≤ K*‖u‖^2 := by
  obtain ⟨hLo,hHi⟩ := (hg.2 y hy).2 (frameVector e y u)
  rw [metricPair_frameVector_self g e y u hframe] at hLo hHi
  refine ⟨hHi,?_⟩
  simpa only [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] using mul_le_mul_of_nonneg_left hLo hK.le

lemma frameVector_mem_unitDisk (g : MetricField) (e : Frame) (y z : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hz : z ∈ Metric.closedBall (0:X) 1) : frameVector e y z ∈ disk g y 1 := by
  have hzNorm : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  change metricPair g y (frameVector e y z) (frameVector e y z) ≤ (1:ℝ)^2
  rw [metricPair_frameVector_self g e y z hframe]
  nlinarith [norm_nonneg z]

lemma NormalCoordinates.framedNormalMetric_zero {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (z : X) :
    framedNormalMetric g e expMap y 0 z = 1 := by
  ext i j
  change normalPullbackMetricPair g expMap y 0 (frameVector e y z) (e y i) (e y j) = if i = j then 1 else 0
  rw [hN.normalPullbackMetricPair_zero hy e hframe,hframe]

lemma NormalCoordinates.framedNormalMetric_first_zero {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (hyΩ : y ∈ Ω) (e : Frame)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (z : X) (i j : I) :
    HasDerivAt (fun s : ℝ => framedNormalMetric g e expMap y s z i j) 0 0 :=
  hN.normalPullbackMetricPair_first_zero hΩ hg hK hy hyΩ e hframe (frameVector e y z) (e y i) (e y j)

end ShrinkingSpheres
