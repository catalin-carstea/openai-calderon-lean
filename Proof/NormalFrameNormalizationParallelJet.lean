import Proof.NormalFrameNormalizationGerms
import Proof.NormalPullbackMetric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NormalCoordinatesFrame

/-- Metric compatibility says that the pulled-back metric has zero first
jet along the affine parallel tangent. This is a first-jet identity only. -/
lemma hasDerivAt_normalFrameGramMetric_parallel_zero {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K)
    (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Ω) (a : X) :
    HasDerivAt (fun t => normalFrameGramMetric g (normalFrameParallelCurve g e r y a t)) 0 0 := by
  let p0 : NormalFrameParameter := (y,(r y,frameVectorLinear e y))
  let v0 : NormalFrameParameter := (a,(0,-((connectionBilinear g y a).comp (frameVectorLinear e y))))
  have hM := contDiffAt_normalFrameGramMetric g p0 (fun i j => (h.1 i j).contDiffAt (hΩ.mem_nhds hy))
  have hFM : HasFDerivAt (normalFrameGramMetric g) (fderiv ℝ (normalFrameGramMetric g) p0)
      (normalFrameParallelCurve g e r y a 0) := by
    rw [normalFrameParallelCurve_zero]
    exact (hM.differentiableAt (by simp)).hasFDerivAt
  have htM : HasDerivAt (fun t => normalFrameGramMetric g (normalFrameParallelCurve g e r y a t))
      (fderiv ℝ (normalFrameGramMetric g) p0 v0) 0 :=
    hFM.comp_hasDerivAt 0 (hasDerivAt_normalFrameParallelCurve g e r y a)
  have hZero : fderiv ℝ (normalFrameGramMetric g) p0 v0 = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    have hInner := (htM.clm_apply (hasDerivAt_const (0:ℝ) u)).inner ℝ (hasDerivAt_const (0:ℝ) v)
    simp only [map_zero,add_zero,inner_zero_right,zero_add] at hInner
    have hFunctions : (fun t => inner ℝ (normalFrameGramMetric g (normalFrameParallelCurve g e r y a t) u) v) =
        (fun t => metricPair g (y+t • a) (affineParallelFrame g y a (frameVectorLinear e y) t u)
          (affineParallelFrame g y a (frameVectorLinear e y) t v)) := by
      funext t
      exact normalFrameGramMetric_pair g (normalFrameParallelCurve g e r y a t) u v
    rw [hFunctions] at hInner
    have hc0 := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
    change HasDerivAt (fun t : ℝ => y+t • a) _ 0 at hc0
    have hc : HasDerivAt (fun t : ℝ => y+t • a) a 0 := by simpa only [one_smul,zero_add] using hc0
    have hy0 : y+(0:ℝ) • a ∈ Ω := by simpa only [zero_smul,add_zero] using hy
    have hPair := hasDerivAt_metricPair_curve hΩ h hc
      (hasDerivAt_affineParallelFrame_apply g y a (frameVectorLinear e y) 0 u)
      (hasDerivAt_affineParallelFrame_apply g y a (frameVectorLinear e y) 0 v) hy0
    simp only [zero_smul,add_zero,affineParallelFrame_zero] at hPair
    have hNegU : metricPair g y (-connection g y a (frameVectorLinear e y u)) (frameVectorLinear e y v) =
        -metricPair g y (connection g y a (frameVectorLinear e y u)) (frameVectorLinear e y v) := by
      simp only [← metricBilinear_apply,map_neg,_root_.neg_apply]
    have hNegV : metricPair g y (frameVectorLinear e y u) (-connection g y a (frameVectorLinear e y v)) =
        -metricPair g y (frameVectorLinear e y u) (connection g y a (frameVectorLinear e y v)) := by
      simp only [← metricBilinear_apply,map_neg]
    rw [hNegU,hNegV] at hPair
    have hCompat := connection_metric hΩ h hK hy a (frameVectorLinear e y u) (frameVectorLinear e y v)
    have hVal : metricDifferential g y a (frameVectorLinear e y u) (frameVectorLinear e y v)+
        -metricPair g y (connection g y a (frameVectorLinear e y u)) (frameVectorLinear e y v)+
        -metricPair g y (frameVectorLinear e y u) (connection g y a (frameVectorLinear e y v)) = 0 := by
      linarith only [hCompat]
    rw [hVal] at hPair
    simpa only [zero_apply,inner_zero_left] using hInner.unique hPair
  simpa only [hZero] using htM

/-- Gram normalization preserves the already checked parallel first tangent,
while its higher curves stay genuinely orthonormal. -/
lemma hasDerivAt_normalFrameNormalizedLinear_parallel {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K)
    (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Ω)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (a : X) :
    HasDerivAt (fun t => normalFrameNormalizedLinear g (normalFrameParallelCurve g e r y a t))
      (-((connectionBilinear g y a).comp (frameVectorLinear e y))) 0 := by
  let G : (X →L[ℝ] X) → X →L[ℝ] X := fun M => frameOperator (metricGramFrame M)
  have hG : ContDiffAt ℝ ∞ G (ContinuousLinearMap.id ℝ X) := by
    apply contDiffAt_metricGramFrameOperator (fun M : X →L[ℝ] X => M) _ contDiffAt_id
    intro u hu
    exact real_inner_self_pos.mpr hu
  have he0 : ∀ i j,metricPair g y (frameVectorLinear e y (axis i)) (frameVectorLinear e y (axis j)) = if i=j then 1 else 0 :=
    by simpa only [frameVectorLinear_apply,frameVector_axis] using he
  have hM0 : normalFrameGramMetric g (normalFrameParallelCurve g e r y a 0) = ContinuousLinearMap.id ℝ X := by
    rw [normalFrameParallelCurve_zero]
    exact normalFrameGramMetric_eq_id g _ he0
  have hFG : HasFDerivAt G (fderiv ℝ G (ContinuousLinearMap.id ℝ X))
      (normalFrameGramMetric g (normalFrameParallelCurve g e r y a 0)) := by
    rw [hM0]
    exact (hG.differentiableAt (by simp)).hasFDerivAt
  have hGCurve := hFG.comp_hasDerivAt 0 (hasDerivAt_normalFrameGramMetric_parallel_zero hΩ h hK e r hy a)
  simp only [map_zero] at hGCurve
  have ht := (hasDerivAt_affineParallelFrame g y a (frameVectorLinear e y) 0).clm_comp hGCurve
  convert ht using 1
  · rfl
  · simp only [Function.comp_def,hM0,G,frameOperator_metricGramFrame_id,ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.comp_id,zero_add,add_zero]

lemma hasDerivAt_normalizedOrthonormalFrameParameter_parallel {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K)
    (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Ω)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (a : X) :
    HasDerivAt (fun t => normalizedOrthonormalFrameParameter g (normalFrameParallelCurve g e r y a t))
      (a,(0,-((connectionBilinear g y a).comp (frameVectorLinear e y)))) 0 := by
  have hc0 := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  change HasDerivAt (fun t : ℝ => y+t • a) _ 0 at hc0
  have hc : HasDerivAt (fun t : ℝ => y+t • a) a 0 := by simpa only [one_smul,zero_add] using hc0
  exact hc.prodMk ((hasDerivAt_const (0:ℝ) (r y)).prodMk
    (hasDerivAt_normalFrameNormalizedLinear_parallel hΩ h hK e r hy he a))

/-- Every differentiable operator family has the same parallel first jet
after normalization. This keeps the existing gained first-jet producers
compatible with the genuine orthonormal extension. -/
theorem deriv_normalized_normalFrame_parallel_family_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K)
    (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Ω)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (a : X)
    (H : NormalFrameParameter → F) (hH : DifferentiableAt ℝ H (y,(r y,frameVectorLinear e y))) :
    deriv (fun t => H (normalizedOrthonormalFrameParameter g (normalFrameParallelCurve g e r y a t))) 0 =
      deriv (fun t => H (normalFrameParallelCurve g e r y a t)) 0 := by
  let p0 : NormalFrameParameter := (y,(r y,frameVectorLinear e y))
  have hOriginal : HasFDerivAt H (fderiv ℝ H p0) (normalFrameParallelCurve g e r y a 0) := by
    rw [normalFrameParallelCurve_zero]
    exact hH.hasFDerivAt
  have hNormalized : HasFDerivAt H (fderiv ℝ H p0)
      (normalizedOrthonormalFrameParameter g (normalFrameParallelCurve g e r y a 0)) := by
    rw [normalFrameParallelCurve_zero,normalizedOrthonormalFrameParameter_framed g e y (r y) he]
    exact hH.hasFDerivAt
  exact ((hNormalized.comp_hasDerivAt 0
    (hasDerivAt_normalizedOrthonormalFrameParameter_parallel hΩ h hK e r hy he a)).deriv).trans
      ((hOriginal.comp_hasDerivAt 0 (hasDerivAt_normalFrameParallelCurve g e r y a)).deriv.symm)

end ShrinkingSpheres
