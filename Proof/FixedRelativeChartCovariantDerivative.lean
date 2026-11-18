import Proof.RelativeHorizontalAngularCommutation
import Proof.ActualCovariantRotationGraph
import Proof.FrameCurveFirstJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The horizontal/rotation split holds throughout one fixed relative
radius chart, including points whose relative radius is nonzero. -/
lemma fderiv_fixed_relative_actual_parameter_split
    (d : Data) (r0 : ℝ) (y a : X)
    (hr : DifferentiableAt ℝ d.radius y) (hr0 : d.radius y ≠ 0)
    (hL : DifferentiableAt ℝ (frameVectorLinear d.frame) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => d.frame x i) y)
    (hframe : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j =
      -frameConnectionCoefficient d.γ d.frame y a j i) :
    fderiv ℝ (normalFrameRelativeActualParameter d r0) y a =
      normalFrameRelativeHorizontalField d.γ d.radius a (normalFrameRelativeActualParameter d r0 y)+
        ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
          relativeRightRotationL i j (normalFrameRelativeActualParameter d r0 y) := by
  have hQ := ((hasFDerivAt_id (𝕜:=ℝ) y).prodMk hL.hasFDerivAt).prodMk
    ((hr.hasFDerivAt.mul_const r0⁻¹).sub_const 1)
  change HasFDerivAt (normalFrameRelativeActualParameter d r0) _ y at hQ
  have hEval : fderiv ℝ (normalFrameRelativeActualParameter d r0) y a =
      ((a,fderiv ℝ (frameVectorLinear d.frame) y a),fderiv ℝ d.radius y a/r0) := by
    rw [hQ.fderiv]
    change ((a,fderiv ℝ (frameVectorLinear d.frame) y a),r0⁻¹*fderiv ℝ d.radius y a) = _
    rw [div_eq_mul_inv,mul_comm r0⁻¹]
  rw [hEval]
  have hFrame := fderiv_frameVectorLinear_parallel_rotation_split d.γ d.frame y a
    hL he hframe hSkew
  apply Prod.ext
  · apply Prod.ext
    · simp only [normalFrameRelativeActualParameter,normalFrameRelativeHorizontalField,
        relativeHorizontalFieldOfFamilies,relativeRightRotationL_apply,
        Fin.sum_univ_three,Prod.smul_mk,Prod.mk_add_mk,smul_zero,add_zero]
    · simpa [normalFrameRelativeActualParameter,normalFrameRelativeHorizontalField,
        relativeHorizontalFieldOfFamilies,relativeRightRotationL_apply,
        relativeFrameProjectionL,Fin.sum_univ_three,Prod.smul_mk,Prod.mk_add_mk] using hFrame
  · change fderiv ℝ d.radius y a/r0 =
      (1+(d.radius y/r0-1))*fderiv ℝ (fun x => Real.log (d.radius x)) y a+
        ((∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
          relativeRightRotationL i j (normalFrameRelativeActualParameter d r0 y))).2
    have hSum : ((∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
          relativeRightRotationL i j (normalFrameRelativeActualParameter d r0 y))).2 = 0 := by
      simp only [Fin.sum_univ_three,relativeRightRotationL_apply,Prod.smul_mk,Prod.mk_add_mk,
        smul_zero,add_zero]
    rw [hSum,add_zero,logRadius_derivative d.radius y a hr hr0]
    have hh : 1+(d.radius y/r0-1)=d.radius y/r0 := by ring
    rw [hh]
    field_simp

theorem fderiv_fixed_relative_germ_covariant_eq_horizontal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (r0 : ℝ) (y a : X) (H : X → E) (F : NormalFrameRelativeParameter → E)
    (hGerm : H =ᶠ[𝓝 y] fun x => F (normalFrameRelativeActualParameter d r0 x))
    (hr : DifferentiableAt ℝ d.radius y) (hr0 : d.radius y ≠ 0)
    (hL : DifferentiableAt ℝ (frameVectorLinear d.frame) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => d.frame x i) y)
    (hframe : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j =
      -frameConnectionCoefficient d.γ d.frame y a j i)
    (hF : DifferentiableAt ℝ F (normalFrameRelativeActualParameter d r0 y)) :
    fderiv ℝ H y a-
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        normalFrameRelativeAngularDerivative d.γ F i j (normalFrameRelativeActualParameter d r0 y) =
      fderiv ℝ F (normalFrameRelativeActualParameter d r0 y)
        (normalFrameRelativeHorizontalField d.γ d.radius a (normalFrameRelativeActualParameter d r0 y)) := by
  have hQ : DifferentiableAt ℝ (normalFrameRelativeActualParameter d r0) y := by
    exact (differentiableAt_id.prodMk hL).prodMk ((hr.mul_const r0⁻¹).sub_const 1)
  have hDer : fderiv ℝ H y =
      (fderiv ℝ F (normalFrameRelativeActualParameter d r0 y)).comp
        (fderiv ℝ (normalFrameRelativeActualParameter d r0) y) :=
    hGerm.fderiv_eq.trans (hF.hasFDerivAt.comp y hQ.hasFDerivAt).fderiv
  have hOrtho (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hframe i j
  have hN := normalFrameRelativeNormalization_eq_self d.γ
    (normalFrameRelativeActualParameter d r0 y) hOrtho
  rw [hDer,ContinuousLinearMap.comp_apply,
    fderiv_fixed_relative_actual_parameter_split d r0 y a hr hr0 hL he hframe hSkew,map_add,map_sum]
  simp only [map_sum,map_smul,normalFrameRelativeAngularDerivative,hN]
  change _+∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
    (fderiv ℝ F (normalFrameRelativeActualParameter d r0 y)
      (relativeRightRotationL i j (normalFrameRelativeActualParameter d r0 y)))-_ = _
  simp only [relativeRightRotationL_apply,normalFrameRelativeAngularTangent,hN,add_sub_cancel_right]

theorem fixed_relative_covariant_rotation_graph_of_germ (d : Data) (r0 : ℝ) (y a : X)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (F : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hGerm : H =ᶠ[𝓝 y] fun x => F (normalFrameRelativeActualParameter d r0 x))
    (hr : DifferentiableAt ℝ d.radius y) (hr0 : d.radius y ≠ 0)
    (hL : DifferentiableAt ℝ (frameVectorLinear d.frame) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => d.frame x i) y)
    (hframe : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j =
      -frameConnectionCoefficient d.γ d.frame y a j i)
    (hF : DifferentiableAt ℝ F (normalFrameRelativeActualParameter d r0 y))
    (hGraph : ∀ i j : I,∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j
        (F (normalFrameRelativeActualParameter d r0 y) (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (normalFrameRelativeAngularDerivative d.γ F i j (normalFrameRelativeActualParameter d r0 y)
              (sphereSobolevInclusionL 2 1 (by norm_num) u)+
            F (normalFrameRelativeActualParameter d r0 y) (sphereSobolevRotationL 2 i j u))) :
    CoarseCovariantRotationGraph d y a H
      (fderiv ℝ F (normalFrameRelativeActualParameter d r0 y)
        (normalFrameRelativeHorizontalField d.γ d.radius a (normalFrameRelativeActualParameter d r0 y))) := by
  apply coarseCovariantRotationGraph_of_angular d y a H _ _
    (fderiv_fixed_relative_germ_covariant_eq_horizontal d r0 y a H F hGerm hr hr0 hL he hframe hSkew hF)
  intro i j u
  rw [hGerm.eq_of_nhds]
  exact hGraph i j u

end ShrinkingSpheres
