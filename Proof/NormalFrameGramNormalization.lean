import Proof.LocalMetricGramFrame
import Proof.FrameRadiusParameterJet
import Proof.FrameBasis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.NormalCoordinatesFrame

lemma metricGramFrame_id (i : Fin 3) :
    metricGramFrame (ContinuousLinearMap.id ℝ R3) i = coordinateVector i := by
  fin_cases i <;>
    simp [metricGramFrame,metricNormalize,gramSecond,gramThird,metricPair,coordinateVector,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,PiLp.single_apply]

lemma frameOperator_metricGramFrame_id :
    frameOperator (metricGramFrame (ContinuousLinearMap.id ℝ R3)) = ContinuousLinearMap.id ℝ R3 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [frameOperator_apply]
  simp_rw [metricGramFrame_id]
  simpa only [ContinuousLinearMap.id_apply,coordinateVector,ShrinkingSpheres.axis] using ShrinkingSpheres.axis_expansion v

end OAI.AnisotropicCalderon.NormalCoordinatesFrame
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.MetricOperator
open OAI.AnisotropicCalderon.NormalCoordinatesFrame

lemma metricPair_eq_inner_transpose_operator (g : MetricField) (y u v : X) :
    metricPair g y u v = inner ℝ (matrixOperatorMap (g y).transpose u) v := by
  change (∑ i,∑ j,g y i j*u i*v j) = inner ℝ ((g y).transpose.toEuclideanLin u) v
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
    Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.mulVec,Matrix.transpose_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The metric in an arbitrary independent frame parameter. The transpose
makes its inner product agree with the frozen coordinate metric convention. -/
def normalFrameGramMetric (g : MetricField) (p : NormalFrameParameter) : X →L[ℝ] X :=
  p.2.2.adjoint.comp ((matrixOperatorMap (g p.1).transpose).comp p.2.2)

lemma normalFrameGramMetric_pair (g : MetricField) (p : NormalFrameParameter) (u v : X) :
    inner ℝ (normalFrameGramMetric g p u) v = metricPair g p.1 (p.2.2 u) (p.2.2 v) := by
  unfold normalFrameGramMetric
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.comp_apply]
  exact (metricPair_eq_inner_transpose_operator g p.1 _ _).symm

/-- Gram normalization is applied inside the given independent frame, so
it fixes every already orthonormal frame exactly. -/
def normalFrameNormalizedLinear (g : MetricField) (p : NormalFrameParameter) : X →L[ℝ] X :=
  p.2.2.comp (frameOperator (metricGramFrame (normalFrameGramMetric g p)))

def normalizedOrthonormalFrameParameter (g : MetricField) (p : NormalFrameParameter) : NormalFrameParameter :=
  (p.1,(p.2.1,normalFrameNormalizedLinear g p))

lemma frameVector_linear_axes (L : X →L[ℝ] X) (y u : X) :
    frameVector (fun _ i => L (axis i)) y u = L u := by
  have ht : L u = ∑ i,u i • L (axis i) := by
    conv_lhs => rw [← axis_expansion u]
    simp only [map_sum,map_smul]
  exact ht.symm

lemma normalFrameGramMetric_eq_id (g : MetricField) (p : NormalFrameParameter)
    (he : ∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0) :
    normalFrameGramMetric g p = ContinuousLinearMap.id ℝ X := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [normalFrameGramMetric_pair]
  have ht := metricPair_frameVector g (fun _ i => p.2.2 (axis i)) p.1 u v he
  rw [frameVector_linear_axes,frameVector_linear_axes] at ht
  rw [ht]
  simp only [ContinuousLinearMap.id_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma normalFrameNormalizedLinear_eq_self (g : MetricField) (p : NormalFrameParameter)
    (he : ∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0) :
    normalFrameNormalizedLinear g p = p.2.2 := by
  rw [normalFrameNormalizedLinear,normalFrameGramMetric_eq_id g p he,frameOperator_metricGramFrame_id,
    ContinuousLinearMap.comp_id]

lemma normalizedOrthonormalFrameParameter_eq_self (g : MetricField) (p : NormalFrameParameter)
    (he : ∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0) :
    normalizedOrthonormalFrameParameter g p = p := by
  rw [normalizedOrthonormalFrameParameter,normalFrameNormalizedLinear_eq_self g p he]

/-- At every positive symmetric pulled-back metric the normalized frame is
exactly metric-orthonormal, including away from the original parameter. -/
theorem normalFrameNormalizedLinear_orthonormal (g : MetricField) (p : NormalFrameParameter)
    (hs : ∀ u v,metricPair g p.1 (p.2.2 u) (p.2.2 v) = metricPair g p.1 (p.2.2 v) (p.2.2 u))
    (hp : ∀ u : X,u ≠ 0 → 0 < metricPair g p.1 (p.2.2 u) (p.2.2 u)) :
    ∀ i j,metricPair g p.1 (normalFrameNormalizedLinear g p (axis i))
      (normalFrameNormalizedLinear g p (axis j)) = if i=j then 1 else 0 := by
  have hs' : ∀ u v, OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair (normalFrameGramMetric g p) u v =
      OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair (normalFrameGramMetric g p) v u := by
    intro u v
    exact (normalFrameGramMetric_pair g p u v).trans ((hs u v).trans (normalFrameGramMetric_pair g p v u).symm)
  have hp' : ∀ u : X,u ≠ 0 → 0 < OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair (normalFrameGramMetric g p) u u := by
    intro u hu
    rw [OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair,normalFrameGramMetric_pair]
    exact hp u hu
  have hGram := metricGramFrame_isMetricOrthonormalFrame (normalFrameGramMetric g p) hs' hp'
  intro i j
  change metricPair g p.1 (p.2.2 (frameOperator _ (axis i))) (p.2.2 (frameOperator _ (axis j))) = _
  rw [← normalFrameGramMetric_pair]
  change OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair (normalFrameGramMetric g p)
    (frameOperator _ (coordinateVector i)) (frameOperator _ (coordinateVector j)) = _
  rw [frameOperator_coordinateVector,frameOperator_coordinateVector]
  exact hGram i j

lemma contDiffAt_normalFrameGramMetric (g : MetricField) (p : NormalFrameParameter)
    (hg : ∀ i j,ContDiffAt ℝ ∞ (fun x => g x i j) p.1) :
    ContDiffAt ℝ ∞ (normalFrameGramMetric g) p := by
  have hT : ContDiffAt ℝ ∞ (fun q : NormalFrameParameter => (g q.1).transpose) p :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (hg j i).comp p contDiffAt_fst))
  have hL : ContDiffAt ℝ ∞ (fun q : NormalFrameParameter => q.2.2) p := contDiffAt_snd.snd
  have hAdj := ((ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X)).contDiff.contDiffAt).comp p hL
  exact hAdj.clm_comp ((matrixOperatorMap.contDiff.contDiffAt.comp p hT).clm_comp hL)

/-- The normalization is genuinely smooth on the positive-metric locus.
Only local smoothness at the parameter is required by the Gram construction. -/
lemma contDiffAt_normalFrameNormalizedLinear (g : MetricField) (p : NormalFrameParameter)
    (hg : ∀ i j,ContDiffAt ℝ ∞ (fun x => g x i j) p.1)
    (hp : ∀ u : X,u ≠ 0 → 0 < metricPair g p.1 (p.2.2 u) (p.2.2 u)) :
    ContDiffAt ℝ ∞ (normalFrameNormalizedLinear g) p := by
  have hp' : ∀ u : X,u ≠ 0 → 0 < OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair (normalFrameGramMetric g p) u u := by
    intro u hu
    rw [OAI.AnisotropicCalderon.NormalCoordinatesFrame.metricPair,normalFrameGramMetric_pair]
    exact hp u hu
  exact contDiffAt_snd.snd.clm_comp
    (contDiffAt_metricGramFrameOperator (normalFrameGramMetric g) p (contDiffAt_normalFrameGramMetric g p hg) hp')

lemma contDiffAt_normalizedOrthonormalFrameParameter (g : MetricField) (p : NormalFrameParameter)
    (hg : ∀ i j,ContDiffAt ℝ ∞ (fun x => g x i j) p.1)
    (hp : ∀ u : X,u ≠ 0 → 0 < metricPair g p.1 (p.2.2 u) (p.2.2 u)) :
    ContDiffAt ℝ ∞ (normalizedOrthonormalFrameParameter g) p :=
  contDiffAt_fst.prodMk (contDiffAt_snd.fst.prodMk (contDiffAt_normalFrameNormalizedLinear g p hg hp))

end ShrinkingSpheres
