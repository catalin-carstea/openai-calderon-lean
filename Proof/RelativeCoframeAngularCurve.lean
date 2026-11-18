import Proof.RelativeCoframeSobolevMultiplier
import Proof.RelativeAngularDerivativeCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation

lemma Elliptic.relativeCoframeValue_angular_curve {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (a : X) (k : I)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω) (i j : I) (θ : ℝ) :
    normalFrameRelativeCoframeValue g a k (normalFrameRelativeAngularCurve g p i j θ) =
      metricPair g p.1.1 a ((normalFrameRelativeNormalization g p).1.2
        (coordinateRotationIsometry i j θ (axis k))) := by
  have he := h.normalFrameRelativeAngularCurve_orthonormal hK p hp i j θ
  change normalFrameRelativeCoframeValue g a k
    ((p.1.1,(normalFrameRelativeAngularCurve g p i j θ).1.2),0) = _
  rw [normalFrameRelativeCoframeValue_orthonormal g a k p.1.1 _ he]
  rfl

lemma rotationVectorL_axis (i j k : I) : rotationVectorL i j (axis k) =
    (if k=i then axis j else 0)-(if k=j then axis i else 0) := by
  have hc (l : I) : (EuclideanSpace.proj (𝕜:=ℝ) l : X →L[ℝ] ℝ) (axis k) = if k=l then 1 else 0 := by
    simp [axis,PiLp.proj_apply,PiLp.single_apply,eq_comm]
  simp only [rotationVectorL,_root_.sub_apply,ContinuousLinearMap.smulRight_apply,hc]
  split_ifs <;> simp only [one_smul,zero_smul]

lemma Elliptic.hasDerivAt_relativeCoframeValue_angular {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (a : X) (k : I)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω) (i j : I) :
    HasDerivAt (fun θ => normalFrameRelativeCoframeValue g a k (normalFrameRelativeAngularCurve g p i j θ))
      ((if k=i then normalFrameRelativeCoframeValue g a j p else 0)-
        (if k=j then normalFrameRelativeCoframeValue g a i p else 0)) 0 := by
  let L := (normalFrameRelativeNormalization g p).1.2
  let C : X →L[ℝ] ℝ := metricBilinear g p.1.1 a
  have hR := (hasDerivAt_const (0:ℝ) L).clm_comp (hasDerivAt_coordinateRotationOperator_zero i j)
  have hV := hR.clm_apply (hasDerivAt_const (0:ℝ) (axis k))
  have hD := C.hasFDerivAt.comp_hasDerivAt 0 hV
  have hValue : (fun θ => normalFrameRelativeCoframeValue g a k (normalFrameRelativeAngularCurve g p i j θ)) =
      (fun θ => C (L (coordinateRotationIsometry i j θ (axis k)))) := by
    funext θ
    simpa only [C,metricBilinear_apply] using h.relativeCoframeValue_angular_curve hK a k p hp i j θ
  have hCoeff (l : I) : normalFrameRelativeCoframeValue g a l p=C (L (axis l)) := by
    dsimp only [C]
    rw [metricBilinear_apply]
    rfl
  rw [hValue]
  convert hD using 1
  · rfl
  · simp only [ContinuousLinearMap.zero_comp,zero_add,ContinuousLinearMap.comp_apply,map_zero,add_zero,
      rotationVectorL_axis,map_sub]
    simp only [hCoeff]
    split_ifs <;> simp only [map_zero]

lemma sum_rotation_coordinates {E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : I → ℝ) (T : I → E) (i j : I) :
    (∑ k : I,((if k=i then q j else 0)-(if k=j then q i else 0)) • T k) =
      ∑ k : I,q k • ((if k=j then T i else 0)-(if k=i then T j else 0)) := by
  simp only [sub_smul,smul_sub,ite_smul,smul_ite,zero_smul,smul_zero,
    Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end ShrinkingSpheres
