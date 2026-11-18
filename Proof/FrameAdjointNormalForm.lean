import Proof.FrameAdjointLinearity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact transport of one shared axis normal form into the actual orthonormal
    frame, using the SAME error operators rather than choosing new point witnesses. -/
theorem frame_adjoint_normal_form_of_axes (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (J : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i : I)
    (φ : Field) (L : ℂ →L[ℝ] ℝ) (v : SphereSobolev 1)
    (hAxis : ∀ a,(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (modelBoundaryAdjointL (fixedCenterCoefficient Q d.γ d.frame y (axis a)) (d.radius y)
          (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis a)) v+
        firstBoundaryAdjointCorrectionL (fixedCenterCoefficient Q d.γ d.frame y (axis a))
          (firstRadialCorrectionL d y) (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (axis a))
            (sphereSobolevInclusionL 1 0 (by norm_num) v)+J a v) =ᵐ[sphereProbability]
        fun w : UnitSphere => L (adjointField d.adjoint a φ (y,frameVector d.frame y w.val))) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (modelBoundaryAdjointL (coordinateBoundaryCoefficients Q i) (d.radius y)
          (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) v+
        firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q i) (firstRadialCorrectionL d y)
          (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i))
            (sphereSobolevInclusionL 1 0 (by norm_num) v)+
        (∑ a : I,d.frame y i a • J a) v) =ᵐ[sphereProbability]
        fun w : UnitSphere => L (frameAdjointField d.adjoint d.frame i φ (y,frameVector d.frame y w.val)) := by
  let ell := fderiv ℝ (fun x => Real.log (d.radius x)) y
  let c : I → ℝ := fun a => d.frame y i a
  let P (a : I) := fixedCenterCoefficient Q d.γ d.frame y (axis a)
  let Iv := sphereSobolevInclusionL 1 0 (by norm_num) v
  let T (a : I) := modelBoundaryAdjointL (P a) (d.radius y) (ell (axis a))+
    (firstBoundaryAdjointCorrectionL (P a) (firstRadialCorrectionL d y) (d.radius y) (ell (axis a))).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))+J a
  have hSum := frame_adjoint_operator_realization d y i T φ L v hAxis
  have hModelSum : modelBoundaryAdjointL (coordinateBoundaryCoefficients Q i) (d.radius y) (ell (d.frame y i))=
      ∑ a : I,c a • modelBoundaryAdjointL (P a) (d.radius y) (ell (axis a)) := by
    simpa only [fixedCenterCoefficient_frame Q d.γ d.frame y hFrame i] using
      modelBoundaryAdjointL_axis_expansion Q hQ d.γ d.frame y (d.frame y i) (d.radius y) ell
  have hCorrectionSum : firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q i)
      (firstRadialCorrectionL d y) (d.radius y) (ell (d.frame y i))=
      ∑ a : I,c a • firstBoundaryAdjointCorrectionL (P a) (firstRadialCorrectionL d y) (d.radius y) (ell (axis a)) := by
    simpa only [fixedCenterCoefficient_frame Q d.γ d.frame y hFrame i] using
      firstBoundaryAdjointCorrectionL_axis_expansion Q hQ d.γ d.frame y (d.frame y i)
        (firstRadialCorrectionL d y) (d.radius y) ell
  have hModelPoint := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A v) hModelSum
  have hCorrectionPoint := congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => A Iv) hCorrectionSum
  simp only [_root_.sum_apply,_root_.smul_apply] at hModelPoint hCorrectionPoint
  have hPoint : modelBoundaryAdjointL (coordinateBoundaryCoefficients Q i) (d.radius y) (ell (d.frame y i)) v+
      firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q i) (firstRadialCorrectionL d y)
        (d.radius y) (ell (d.frame y i)) Iv+(∑ a : I,c a • J a) v=(∑ a : I,c a • T a) v := by
    simp only [_root_.sum_apply,_root_.smul_apply,T,_root_.add_apply,ContinuousLinearMap.comp_apply,
      smul_add,Finset.sum_add_distrib]
    rw [hModelPoint,hCorrectionPoint]
  rw [← hPoint] at hSum
  exact hSum
end ShrinkingSpheres
