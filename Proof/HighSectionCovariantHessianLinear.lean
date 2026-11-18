import Proof.HighSectionCovariantDerivativeLinear
import Proof.LeadingPrincipalModelSection
import Proof.FrameCoordinateCovectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine angular-section Hessian, bilinear in its fixed physical
base directions and including the base connection correction. -/
def highSectionCovariantHessianLinear (d : Data) (U : X → SphereSobolev 2) (y : X) :
    X →L[ℝ] X →L[ℝ] SphereSobolev 0 :=
  ((ContinuousLinearMap.compL ℝ X (SphereSobolev 1) (SphereSobolev 0))
      (sphereSobolevInclusionL 1 0 (by norm_num))).comp
        (fderiv ℝ (highSectionCovariantDerivativeLinear d U) y)-
    (∑ i : I,∑ j : I,((1/2:ℝ) • frameConnectionLinear d.γ d.frame y i j).smulRight
      ((sphereSobolevRotationL 1 i j).comp (highSectionCovariantDerivativeLinear d U y)))-
    ((ContinuousLinearMap.compL ℝ X X (SphereSobolev 0))
      ((sphereSobolevInclusionL 1 0 (by norm_num)).comp (highSectionCovariantDerivativeLinear d U y))).comp
        (connectionBilinear d.γ y)

lemma highSectionCovariantHessianLinear_apply (d : Data) (U : X → SphereSobolev 2) (y a b : X)
    (hL : DifferentiableAt ℝ (highSectionCovariantDerivativeLinear d U) y) :
    highSectionCovariantHessianLinear d U y a b=
      oneSectionCovariantDerivative d (fun x => highSectionCovariantDerivative d U x b) y a-
        sphereSobolevInclusionL 1 0 (by norm_num)
          (highSectionCovariantDerivative d U y (connection d.γ y a b)) := by
  have hD : fderiv ℝ (fun x => highSectionCovariantDerivativeLinear d U x b) y a=
      fderiv ℝ (highSectionCovariantDerivativeLinear d U) y a b := by
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply,map_zero,zero_add] using
      DFunLike.congr_fun (hL.hasFDerivAt.clm_apply (hasFDerivAt_const b y)).fderiv a
  simp_rw [←highSectionCovariantDerivativeLinear_apply]
  simp only [highSectionCovariantHessianLinear,oneSectionCovariantDerivative,hD,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    _root_.sub_apply,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,_root_.smul_apply,
    frameConnectionLinear_apply,smul_eq_mul,connectionBilinear_apply]

/-- All derivatives of the moving frame cancel against the Hessian's
covector-index connection, before any coefficient estimate is taken. -/
theorem highSectionCovariantHessian_eq_bilinear (d : Data) (U : X → SphereSobolev 2)
    (y : X) (i j : I)
    (hFrame : ∀ k l,metricPair d.γ y (d.frame y k) (d.frame y l)=if k=l then 1 else 0)
    (hL : DifferentiableAt ℝ (highSectionCovariantDerivativeLinear d U) y)
    (he : DifferentiableAt ℝ (fun x => d.frame x j) y) :
    highSectionCovariantHessian d U y i j=
      highSectionCovariantHessianLinear d U y (d.frame y i) (d.frame y j) := by
  let L := highSectionCovariantDerivativeLinear d U
  have hReconstruct : (∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k • d.frame y k)=
      fderiv ℝ (fun x => d.frame x j) y (d.frame y i)+connection d.γ y (d.frame y i) (d.frame y j) := by
    simpa only [frameCoordinateLinear_apply,frameConnectionCoefficient,covariantFrameVector] using
      frameCoordinateLinear_reconstruct d.γ d.frame y
        (covariantFrameVector d.γ d.frame y (d.frame y i) j) hFrame
  have hSum : (∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
      sphereSobolevInclusionL 1 0 (by norm_num) (L y (d.frame y k)))=
      sphereSobolevInclusionL 1 0 (by norm_num)
        (L y (fderiv ℝ (fun x => d.frame x j) y (d.frame y i)+
          connection d.γ y (d.frame y i) (d.frame y j))) := by
    have hh := congrArg (fun v => sphereSobolevInclusionL 1 0 (by norm_num) (L y v)) hReconstruct
    simpa only [map_sum,map_smul] using hh
  rw [highSectionCovariantHessianLinear_apply d U y (d.frame y i) (d.frame y j) hL]
  unfold highSectionCovariantHessian
  simp_rw [←highSectionCovariantDerivativeLinear_apply]
  rw [oneSectionCovariantDerivative_linear_field d L (fun x => d.frame x j) y (d.frame y i) hL he,hSum]
  simp only [map_add]
  abel

end ShrinkingSpheres
