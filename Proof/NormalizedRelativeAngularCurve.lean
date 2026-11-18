import Proof.NormalFrameRelativeNormalization
import Proof.CoordinateRotationOperatorDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation

def normalFrameRelativeAngularCurve (g : MetricField) (p : NormalFrameRelativeParameter)
    (i j : I) (θ : ℝ) : NormalFrameRelativeParameter :=
  ((p.1.1,(normalFrameRelativeNormalization g p).1.2.comp
    (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap),p.2)

def normalFrameRelativeAngularTangent (g : MetricField) (p : NormalFrameRelativeParameter)
    (i j : I) : NormalFrameRelativeParameter :=
  (((0:X),(normalFrameRelativeNormalization g p).1.2.comp (rotationVectorL i j)),0)

lemma normalFrameRelativeAngularCurve_zero (g : MetricField) (p : NormalFrameRelativeParameter) (i j : I) :
    normalFrameRelativeAngularCurve g p i j 0 = normalFrameRelativeNormalization g p := by
  have hRot : (coordinateRotationIsometry i j 0).toContinuousLinearEquiv.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro z
    exact coordinateRotation_zero i j z
  change ((p.1.1,(normalFrameRelativeNormalization g p).1.2.comp
      (coordinateRotationIsometry i j 0).toContinuousLinearEquiv.toContinuousLinearMap),p.2) =
    ((p.1.1,(normalFrameRelativeNormalization g p).1.2),p.2)
  rw [hRot,ContinuousLinearMap.comp_id]

lemma hasDerivAt_normalFrameRelativeAngularCurve (g : MetricField) (p : NormalFrameRelativeParameter) (i j : I) :
    HasDerivAt (normalFrameRelativeAngularCurve g p i j) (normalFrameRelativeAngularTangent g p i j) 0 := by
  unfold normalFrameRelativeAngularCurve normalFrameRelativeAngularTangent
  have hOp := (hasDerivAt_const (0:ℝ) (normalFrameRelativeNormalization g p).1.2).clm_comp
    (hasDerivAt_coordinateRotationOperator_zero i j)
  simpa only [ContinuousLinearMap.zero_comp,zero_add] using
    ((hasDerivAt_const (0:ℝ) p.1.1).prodMk hOp).prodMk (hasDerivAt_const (0:ℝ) p.2)

lemma Elliptic.normalFrameRelativeAngularCurve_orthonormal {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (p : NormalFrameRelativeParameter)
    (hp : p ∈ normalFrameRelativePositiveDomain Ω) (i j : I) (θ : ℝ) :
    ∀ k l,metricPair g p.1.1 ((normalFrameRelativeAngularCurve g p i j θ).1.2 (axis k))
      ((normalFrameRelativeAngularCurve g p i j θ).1.2 (axis l)) = if k=l then 1 else 0 := by
  let pn := normalFrameRelativeNormalization g p
  have he := h.normalFrameRelativeNormalization_orthonormal hK p hp
  intro k l
  change metricPair g p.1.1 (pn.1.2 (coordinateRotationIsometry i j θ (axis k)))
    (pn.1.2 (coordinateRotationIsometry i j θ (axis l))) = _
  rw [metricPair_orthonormal_linear g (p.1.1,(0,pn.1.2)) he]
  rw [(coordinateRotationIsometry i j θ).inner_map_map]
  simp [axis,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,PiLp.single_apply,Pi.single_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def normalFrameRelativeAngularDerivative (g : MetricField) (F : NormalFrameRelativeParameter → E)
    (i j : I) (p : NormalFrameRelativeParameter) : E :=
  fderiv ℝ F (normalFrameRelativeNormalization g p) (normalFrameRelativeAngularTangent g p i j)

lemma normalFrameRelativeAngularDerivative_eq_curve (g : MetricField) (F : NormalFrameRelativeParameter → E)
    (i j : I) (p : NormalFrameRelativeParameter)
    (hF : DifferentiableAt ℝ F (normalFrameRelativeNormalization g p)) :
    normalFrameRelativeAngularDerivative g F i j p =
      deriv (fun θ => F (normalFrameRelativeAngularCurve g p i j θ)) 0 := by
  have hF0 : HasFDerivAt F (fderiv ℝ F (normalFrameRelativeNormalization g p))
      (normalFrameRelativeAngularCurve g p i j 0) := by
    rw [normalFrameRelativeAngularCurve_zero]
    exact hF.hasFDerivAt
  have hD := hF0.comp_hasDerivAt 0 (hasDerivAt_normalFrameRelativeAngularCurve g p i j)
  simpa only [Function.comp_def,normalFrameRelativeAngularDerivative] using hD.deriv.symm

end ShrinkingSpheres
