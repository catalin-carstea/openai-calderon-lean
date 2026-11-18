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

/-- The genuine H1-to-H0 covariant section derivative, with its physical
direction packaged as an actual continuous linear map. -/
def oneSectionCovariantDerivativeLinear (d : Data) (U : X → SphereSobolev 1) (y : X) :
    X →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevInclusionL 1 0 (by norm_num)).comp (fderiv ℝ U y)-
    ∑ i : I,∑ j : I,((1/2:ℝ) • frameConnectionLinear d.γ d.frame y i j).smulRight
      (sphereSobolevRotationL 1 i j (U y))

lemma oneSectionCovariantDerivativeLinear_apply (d : Data) (U : X → SphereSobolev 1) (y a : X) :
    oneSectionCovariantDerivativeLinear d U y a=oneSectionCovariantDerivative d U y a := by
  simp only [oneSectionCovariantDerivativeLinear,oneSectionCovariantDerivative,
    _root_.sub_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,frameConnectionLinear_apply,smul_eq_mul]

lemma contDiffOn_oneSectionCovariantDerivativeLinear {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev 1) (hU : ContDiffOn ℝ ∞ U Y) :
    ContDiffOn ℝ ∞ (oneSectionCovariantDerivativeLinear d U) Y := by
  have hΓ (i j : I) : ContDiffOn ℝ ∞ (fun x => frameConnectionLinear d.γ d.frame x i j) Y := by
    apply contDiffOn_clm_apply.mpr
    intro a
    simpa only [frameConnectionLinear_apply] using
      hg.contDiffOn_frameConnection hY hK d.frame he (fun _ => a) contDiffOn_const i j
  exact (contDiffOn_const.clm_comp (hU.fderiv_of_isOpen hY (by simp))).sub
    (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      ((hΓ i j).const_smul (1/2:ℝ)).smulRight
        ((sphereSobolevRotationL 1 i j).contDiff.comp_contDiffOn hU))))

end ShrinkingSpheres
