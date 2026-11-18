import Proof.OrthonormalNormalFrameCoefficient
import Proof.NormalFrameRotationCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation

lemma metricPair_orthonormal_linear (g : MetricField) (p : NormalFrameParameter)
    (he : ∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0)
    (u v : X) : metricPair g p.1 (p.2.2 u) (p.2.2 v) = inner ℝ u v := by
  rw [← normalFrameGramMetric_pair,normalFrameGramMetric_eq_id g p he,ContinuousLinearMap.id_apply]

lemma contDiffAt_normalization_at_orthonormal (g : MetricField) (p : NormalFrameParameter)
    (hg : ∀ i j,ContDiffAt ℝ ∞ (fun x => g x i j) p.1)
    (he : ∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0) :
    ContDiffAt ℝ ∞ (normalizedOrthonormalFrameParameter g) p := by
  apply contDiffAt_normalizedOrthonormalFrameParameter g p hg
  intro u hu
  rw [metricPair_orthonormal_linear g p he]
  exact real_inner_self_pos.mpr hu

lemma normalizedOrthonormalFrameParameter_framed (g : MetricField) (e : Frame) (y : X) (r : ℝ)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) :
    normalizedOrthonormalFrameParameter g (y,(r,frameVectorLinear e y)) =
      (y,(r,frameVectorLinear e y)) :=
  normalizedOrthonormalFrameParameter_eq_self g _
    (by simpa only [frameVectorLinear_apply,frameVector_axis] using he)

/-- Normalization agrees with every actual moving orthonormal frame in a
neighborhood of the center, so all ordinary derivatives of its restriction
are those of the unchanged actual family. -/
lemma normalizedOrthonormalFrameParameter_actual_germ {Ω : Set X} (hΩ : IsOpen Ω)
    (g : MetricField) (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Ω)
    (he : ∀ x ∈ Ω,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0) (a : X) :
    (fun t => normalizedOrthonormalFrameParameter g (normalFrameActualCurve e r y a t)) =ᶠ[𝓝 (0:ℝ)]
      normalFrameActualCurve e r y a := by
  have hc : ContinuousAt (fun t : ℝ => y+t • a) 0 := continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hCenter : ∀ᶠ t in 𝓝 (0:ℝ),y+t • a ∈ Ω := by
    apply hc.eventually
    change Ω ∈ 𝓝 (y+(0:ℝ) • a)
    simpa only [zero_smul,add_zero] using hΩ.mem_nhds hy
  filter_upwards [hCenter] with t ht
  exact normalizedOrthonormalFrameParameter_framed g e (y+t • a) (r (y+t • a)) (he _ ht)

lemma normalizedOrthonormalFrameParameter_radius (g : MetricField) (e : Frame) (r : X → ℝ) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (t : ℝ) :
    normalizedOrthonormalFrameParameter g (normalFrameRadiusCurve e r y t) = normalFrameRadiusCurve e r y t :=
  normalizedOrthonormalFrameParameter_framed g e y ((1+t)*r y) he

lemma normalizedOrthonormalFrameParameter_rotation (g : MetricField) (e : Frame) (r : X → ℝ) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (i j : I) (t : ℝ) :
    normalizedOrthonormalFrameParameter g (normalFrameRotationCurve e r y i j t) = normalFrameRotationCurve e r y i j t := by
  let p0 : NormalFrameParameter := (y,(r y,frameVectorLinear e y))
  have he0 : ∀ k l,metricPair g p0.1 (p0.2.2 (axis k)) (p0.2.2 (axis l)) = if k=l then 1 else 0 :=
    by simpa only [p0,frameVectorLinear_apply,frameVector_axis] using he
  apply normalizedOrthonormalFrameParameter_eq_self
  intro k l
  change metricPair g y ((frameVectorLinear e y) (coordinateRotationIsometry i j t (axis k)))
    ((frameVectorLinear e y) (coordinateRotationIsometry i j t (axis l))) = _
  rw [metricPair_orthonormal_linear g p0 he0]
  rw [(coordinateRotationIsometry i j t).inner_map_map]
  simp [axis,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,PiLp.single_apply,Pi.single_apply]

/-- Exact family agreement can be transported through any operator-valued
caller, including a moving multiplier and its native adjoint. -/
lemma normalFrame_normalized_actual_family_germ {F : Type*} {Ω : Set X} (hΩ : IsOpen Ω)
    (g : MetricField) (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Ω)
    (he : ∀ x ∈ Ω,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (a : X) (H : NormalFrameParameter → F) :
    (fun t => H (normalizedOrthonormalFrameParameter g (normalFrameActualCurve e r y a t))) =ᶠ[𝓝 (0:ℝ)]
      (fun t => H (normalFrameActualCurve e r y a t)) := by
  filter_upwards [normalizedOrthonormalFrameParameter_actual_germ hΩ g e r hy he a] with t ht
  exact congrArg H ht

end ShrinkingSpheres
