import Proof.HighSectionCovariantDerivativeLinear
import Proof.Localization
import Proof.SupportedOperatorCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.PrincipalCommutator OperatorForms

lemma highSectionCovariantDerivative_zero_off (d : Data) (U : X → SphereSobolev 2)
    (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0) (a x : X) (hx : x ∉ S) :
    highSectionCovariantDerivative d U x a=0 := by
  have hD : fderiv ℝ U x a=0 := directional_eq_zero_off U S hS h0 a x hx
  simp only [highSectionCovariantDerivative,h0 x hx,hD,map_zero,smul_zero,
    Finset.sum_const_zero,sub_zero]

lemma oneSectionCovariantDerivative_zero_off (d : Data) (U : X → SphereSobolev 1)
    (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0) (a x : X) (hx : x ∉ S) :
    oneSectionCovariantDerivative d U x a=0 := by
  have hD : fderiv ℝ U x a=0 := directional_eq_zero_off U S hS h0 a x hx
  simp only [oneSectionCovariantDerivative,h0 x hx,hD,map_zero,smul_zero,
    Finset.sum_const_zero,sub_zero]

/-- A locally smooth actual covariant derivative of a supported section
is a globally smooth supported section, even with arbitrary exterior data. -/
theorem contDiff_supported_highSectionCovariantDerivative {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) (a : X) :
    ContDiff ℝ ∞ (fun x => highSectionCovariantDerivative d U x a) ∧
      ∀ x ∉ S,highSectionCovariantDerivative d U x a=0 := by
  have hLocal : ContDiffOn ℝ ∞ (fun x => highSectionCovariantDerivative d U x a) Y := by
    simpa only [highSectionCovariantDerivativeLinear_apply] using
      (contDiffOn_highSectionCovariantDerivativeLinear hY d hg hK he U hU.contDiffOn).clm_apply
        (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => a) Y)
  have hOff := highSectionCovariantDerivative_zero_off d U S hS h0 a
  exact ⟨contDiff_of_tsupport_subset hY _ hLocal
    ((tsupport_subset_of_zero_off _ S hS hOff).trans hSY),hOff⟩

lemma contDiffOn_oneSectionCovariantDerivative {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev 1) (hU : ContDiffOn ℝ ∞ U Y) (a : X) :
    ContDiffOn ℝ ∞ (fun x => oneSectionCovariantDerivative d U x a) Y := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ U) Y := hU.fderiv_of_isOpen hY (by simp)
  have hDa : ContDiffOn ℝ ∞ (fun x => fderiv ℝ U x a) Y := hD.clm_apply contDiffOn_const
  have hΓ (i j : I) := hg.contDiffOn_frameConnection hY hK d.frame he
    (fun _ => a) contDiffOn_const i j
  exact ((sphereSobolevInclusionL 1 0 (by norm_num)).contDiff.comp_contDiffOn hDa).sub
    (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => (1/2:ℝ)) Y).mul (hΓ i j)).smul
        ((sphereSobolevRotationL 1 i j).contDiff.comp_contDiffOn hU))))

theorem contDiff_supported_oneSectionCovariantDerivative {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev 1) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) (a : X) :
    ContDiff ℝ ∞ (fun x => oneSectionCovariantDerivative d U x a) ∧
      ∀ x ∉ S,oneSectionCovariantDerivative d U x a=0 := by
  have hLocal := contDiffOn_oneSectionCovariantDerivative hY d hg hK he U hU.contDiffOn a
  have hOff := oneSectionCovariantDerivative_zero_off d U S hS h0 a
  exact ⟨contDiff_of_tsupport_subset hY _ hLocal
    ((tsupport_subset_of_zero_off _ S hS hOff).trans hSY),hOff⟩

end ShrinkingSpheres
