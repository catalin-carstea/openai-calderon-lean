import Proof.NormalFrameMovingMultiplierJetBounds
import Proof.NormalMetricDerivative
import Proof.NormalPullbackMetric
import Proof.FrameCoordinateCovectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def normalFrameCoframeValue (g : MetricField) (v : X) (j : I) (p : NormalFrameParameter) : ℝ :=
  metricPair g p.1 v (p.2.2 (axis j))

def normalFrameCoframeMultiplier (Q : SmoothCoefficientJets 3) (g : MetricField) (v : X) (j : I)
    (p : NormalFrameParameter) : SmoothCoefficientJets 3 := normalFrameCoframeValue g v j p • Q

lemma contDiffAt_normalFrameCoframeValue {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (v : X) (j : I) {p : NormalFrameParameter} (hp : p.1 ∈ Ω) :
    ContDiffAt ℝ ∞ (normalFrameCoframeValue g v j) p := by
  have hL : ContDiff ℝ ∞ (fun q : NormalFrameParameter => q.2.2 (axis j)) :=
    contDiff_snd.snd.clm_apply contDiff_const
  have hG (a b : I) : ContDiffAt ℝ ∞ (fun q : NormalFrameParameter => g q.1 a b) p :=
    ((h.1 a b).contDiffAt (hΩ.mem_nhds hp)).comp p contDiffAt_fst
  have hEntry (b : I) : ContDiff ℝ ∞ (fun q : NormalFrameParameter => q.2.2 (axis j) b) :=
    (EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.comp hL
  change ContDiffAt ℝ ∞ (fun q : NormalFrameParameter => ∑ a,∑ b,g q.1 a b*v a*(q.2.2 (axis j)) b) p
  exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
    ((hG a b).mul contDiffAt_const).mul (hEntry b).contDiffAt))

lemma normalFrameCoframeValue_point (g : MetricField) (e : Frame) (r : X → ℝ) (y v : X) (j : I) :
    normalFrameCoframeValue g v j (y,(r y,frameVectorLinear e y)) = frameCoordinateLinear g e y j v := by
  rw [frameCoordinateLinear_apply]
  simp only [normalFrameCoframeValue,frameVectorLinear_apply,frameVector_axis]

lemma normalFrameCoframeValue_radius (g : MetricField) (e : Frame) (r : X → ℝ) (y v : X) (j : I) :
    (fun t => normalFrameCoframeValue g v j (normalFrameRadiusCurve e r y t)) =
      (fun _ : ℝ => frameCoordinateLinear g e y j v) := by
  funext t
  rw [frameCoordinateLinear_apply]
  simp only [normalFrameCoframeValue,normalFrameRadiusCurve,frameVectorLinear_apply,frameVector_axis]

lemma hasDerivAt_normalFrameCoframeValue_rotation (g : MetricField) (e : Frame) (r : X → ℝ)
    (y v : X) (j i k : I) :
    HasDerivAt (fun t => normalFrameCoframeValue g v j (normalFrameRotationCurve e r y i k t))
      (metricPair g y v (frameVectorLinear e y (rotationVectorL i k (axis j)))) 0 := by
  let C : X →L[ℝ] ℝ := metricBilinear g y v
  have hL := (hasDerivAt_const (0:ℝ) (frameVectorLinear e y)).clm_comp
    (hasDerivAt_coordinateRotationOperator_zero i k)
  have hV := hL.clm_apply (hasDerivAt_const (0:ℝ) (axis j))
  have ht := C.hasFDerivAt.comp_hasDerivAt 0 hV
  simpa only [Function.comp_def,C,metricBilinear_apply,normalFrameCoframeValue,normalFrameRotationCurve,
    ContinuousLinearMap.zero_comp,zero_add,map_zero,add_zero,ContinuousLinearMap.comp_apply] using ht

lemma hasDerivAt_normalFrameCoframeValue_parallel {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Ω) (v a : X) (j : I) :
    HasDerivAt (fun t => normalFrameCoframeValue g v j (normalFrameParallelCurve g e r y a t))
      (metricDifferential g y a v (e y j)-metricPair g y v (connection g y a (e y j))) 0 := by
  have hc0 := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  change HasDerivAt (fun t : ℝ => y+t • a) _ 0 at hc0
  have hc : HasDerivAt (fun t : ℝ => y+t • a) a 0 := by simpa only [one_smul,zero_add] using hc0
  have hV := hasDerivAt_affineParallelFrame_apply g y a (frameVectorLinear e y) 0 (axis j)
  have hy0 : y+(0:ℝ) • a ∈ Ω := by simpa only [zero_smul,add_zero] using hy
  have ht := hasDerivAt_metricPair_curve hΩ h hc (hasDerivAt_const (0:ℝ) v) hV hy0
  convert ht using 1
  · rfl
  · simp only [zero_smul,add_zero,affineParallelFrame_zero,frameVectorLinear_apply,frameVector_axis]
    simp only [metricPair]
    simp only [PiLp.neg_apply,PiLp.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,
      mul_neg,Finset.sum_neg_distrib]
    ring

lemma normalFrameCoframeMultiplier_point (Q : SmoothCoefficientJets 3) (g : MetricField)
    (e : Frame) (r : X → ℝ) (y v : X) (j : I) :
    normalFrameCoframeMultiplier Q g v j (y,(r y,frameVectorLinear e y)) =
      frameCoordinateLinear g e y j v • Q := by
  unfold normalFrameCoframeMultiplier
  rw [normalFrameCoframeValue_point]

/-- The multiplier is the actual constant coframe coefficient on the ball,
with a single fixed compact jet Q chosen to represent one there. -/
lemma normalFrameCoframeMultiplier_germ (Q : SmoothCoefficientJets 3)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 3 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (r : X → ℝ) (y v : X) (j : I)
    (z : X) (hz : z ∈ Metric.closedBall (0:X) 1) :
    coefficientValue 3 (normalFrameCoframeMultiplier Q g v j (y,(r y,frameVectorLinear e y))) =ᶠ[𝓝 z]
      (fun _ => frameCoordinateLinear g e y j v) := by
  rw [normalFrameCoframeMultiplier_point,coefficientValue_smul]
  filter_upwards [hQ z hz] with w hw
  change frameCoordinateLinear g e y j v*coefficientValue 3 Q w = _
  rw [hw,mul_one]

end ShrinkingSpheres
