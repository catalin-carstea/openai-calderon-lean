import Proof.OneSectionCovariantDerivative
import Proof.CoarseCovariantJetFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine H2-to-H1 covariant section derivative, with its physical
direction packaged as an actual continuous linear map. -/
def highSectionCovariantDerivativeLinear (d : Data) (U : X → SphereSobolev 2) (y : X) :
    X →L[ℝ] SphereSobolev 1 :=
  (sphereSobolevInclusionL 2 1 (by norm_num)).comp (fderiv ℝ U y)-
    ∑ i : I,∑ j : I,((1/2:ℝ) • frameConnectionLinear d.γ d.frame y i j).smulRight
      (sphereSobolevRotationL 2 i j (U y))

lemma highSectionCovariantDerivativeLinear_apply (d : Data) (U : X → SphereSobolev 2) (y a : X) :
    highSectionCovariantDerivativeLinear d U y a=highSectionCovariantDerivative d U y a := by
  simp only [highSectionCovariantDerivativeLinear,highSectionCovariantDerivative,
    _root_.sub_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,frameConnectionLinear_apply,smul_eq_mul]

lemma contDiffOn_highSectionCovariantDerivativeLinear {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y) :
    ContDiffOn ℝ ∞ (highSectionCovariantDerivativeLinear d U) Y := by
  have hΓ (i j : I) : ContDiffOn ℝ ∞ (fun x => frameConnectionLinear d.γ d.frame x i j) Y := by
    apply contDiffOn_clm_apply.mpr
    intro a
    simpa only [frameConnectionLinear_apply] using
      hg.contDiffOn_frameConnection hY hK d.frame he (fun _ => a) contDiffOn_const i j
  exact (contDiffOn_const.clm_comp (hU.fderiv_of_isOpen hY (by simp))).sub
    (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      ((hΓ i j).const_smul (1/2:ℝ)).smulRight
        ((sphereSobolevRotationL 2 i j).contDiff.comp_contDiffOn hU))))

/-- The moving physical direction contributes exactly its ordinary
derivative. This term must be canceled with the covector-index connection
before estimating a frame Hessian. -/
lemma oneSectionCovariantDerivative_linear_field (d : Data)
    (F : X → X →L[ℝ] SphereSobolev 1) (V : X → X) (y a : X)
    (hF : DifferentiableAt ℝ F y) (hV : DifferentiableAt ℝ V y) :
    oneSectionCovariantDerivative d (fun x => F x (V x)) y a=
      oneSectionCovariantDerivative d (fun x => F x (V y)) y a+
        sphereSobolevInclusionL 1 0 (by norm_num) (F y (fderiv ℝ V y a)) := by
  have hD : fderiv ℝ (fun x => F x (V x)) y a=
      F y (fderiv ℝ V y a)+fderiv ℝ F y a (V y) := by
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply] using
      DFunLike.congr_fun (hF.hasFDerivAt.clm_apply hV.hasFDerivAt).fderiv a
  have hD0 : fderiv ℝ (fun x => F x (V y)) y a=fderiv ℝ F y a (V y) := by
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply,map_zero,zero_add] using
      DFunLike.congr_fun (hF.hasFDerivAt.clm_apply (hasFDerivAt_const (V y) y)).fderiv a
  simp only [oneSectionCovariantDerivative,hD,hD0,map_add]
  abel

end ShrinkingSpheres
