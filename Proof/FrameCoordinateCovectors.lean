import Proof.FramePullback
import Proof.CurvatureOperatorBounds
import Proof.UniformNormalGeodesicBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace ShrinkingSpheres

/-- The coframe at one center, as actual bounded linear functionals. -/
def frameCoordinateLinear (g : MetricField) (e : Frame) (y : X) (j : I) : X →L[ℝ] ℝ :=
  (metricBilinear g y).flip (e y j)

lemma frameCoordinateLinear_apply (g : MetricField) (e : Frame) (y v : X) (j : I) :
    frameCoordinateLinear g e y j v = metricPair g y v (e y j) :=
  metricBilinear_apply g y v (e y j)

lemma frameCoordinateLinear_reconstruct (g : MetricField) (e : Frame) (y v : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    (∑ j : I,frameCoordinateLinear g e y j v • e y j) = v := by
  simpa only [frameBasis_apply,frameBasis_repr,frameCoordinateLinear_apply] using
    (frameBasis g e y he).sum_repr v

/-- A coframe size bound uses ellipticity and metric values alone. -/
theorem Elliptic.norm_frameCoordinateLinear_le {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 1 ≤ K) {y : X} (hy : y ∈ Ω) (e : Frame)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (M0 : ℝ) (hM0 : 0 ≤ M0) (hEntry : ∀ i j,|g y i j| ≤ M0) (j : I) :
    ‖frameCoordinateLinear g e y j‖ ≤ 9*M0*K := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hSphere : e y j ∈ sphereAt g y := by
    change metricPair g y (e y j) (e y j) = 1
    exact (he j j).trans (if_pos rfl)
  have hSq := hg.sphere_norm_sq_bound hKpos hy hSphere
  have hFrame : ‖e y j‖ ≤ K := by
    apply (sq_le_sq₀ (norm_nonneg _) hKpos.le).mp
    nlinarith only [hSq,hK,sq_nonneg (K-1)]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [Real.norm_eq_abs,frameCoordinateLinear_apply]
  calc
    _ ≤ 9*M0*‖v‖*‖e y j‖ := metricPair_abs_le_of_entry_bound g y M0 hM0 hEntry v (e y j)
    _ ≤ 9*M0*‖v‖*K := by gcongr
    _ = _ := by ring

end ShrinkingSpheres
