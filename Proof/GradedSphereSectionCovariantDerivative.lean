import Proof.SupportedCovariantSections
import Proof.Archive.SphereSobolevConormalRotationDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OperatorForms

/-- Actual covariant differentiation at an arbitrary genuine Sobolev
grade, reducing the declared angular regularity by one. -/
def gradedSphereSectionCovariantDerivative (s : ℝ) (d : Data) (U : X → SphereSobolev s) (y a : X) :
    SphereSobolev (s-1) :=
  sphereSobolevInclusionL s (s-1) (by linarith) (fderiv ℝ U y a)-
    ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
      sphereSobolevRotationL s i j (U y)

lemma gradedSphereSectionCovariantDerivative_inclusion (s t : ℝ) (hst : t ≤ s)
    (d : Data) (U : X → SphereSobolev s) (y a : X) (hU : DifferentiableAt ℝ U y) :
    sphereSobolevInclusionL (s-1) (t-1) (by linarith) (gradedSphereSectionCovariantDerivative s d U y a)=
      gradedSphereSectionCovariantDerivative t d
        (fun x => sphereSobolevInclusionL s t hst (U x)) y a := by
  have hD : fderiv ℝ (fun x => sphereSobolevInclusionL s t hst (U x)) y a=
      sphereSobolevInclusionL s t hst (fderiv ℝ U y a) := by
    simpa only [ContinuousLinearMap.comp_apply,Function.comp_def] using DFunLike.congr_fun
      ((sphereSobolevInclusionL s t hst).hasFDerivAt.comp y hU.hasFDerivAt).fderiv a
  have hR (i j : I) := DFunLike.congr_fun (sphereSobolevRotationL_inclusion s t hst i j) (U y)
  simp only [ContinuousLinearMap.comp_apply] at hR
  simp only [gradedSphereSectionCovariantDerivative,hD,map_sub,map_sum,map_smul,
    sphereSobolevInclusionL_trans_apply]
  simp only [hR]

lemma gradedSphereSectionCovariantDerivative_two (d : Data) (U : X → SphereSobolev 2) (y a : X) :
    gradedSphereSectionCovariantDerivative 2 d U y a=highSectionCovariantDerivative d U y a := by
  have hI : sphereSobolevInclusionL 2 ((2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 2 1 (by norm_num) := by congr 1 <;> norm_num
  simp only [gradedSphereSectionCovariantDerivative,highSectionCovariantDerivative,hI]

lemma gradedSphereSectionCovariantDerivative_zero_off (s : ℝ) (d : Data) (U : X → SphereSobolev s)
    (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0) (a x : X) (hx : x ∉ S) :
    gradedSphereSectionCovariantDerivative s d U x a=0 := by
  have hD : fderiv ℝ U x a=0 := OperatorForms.directional_eq_zero_off U S hS h0 a x hx
  simp only [gradedSphereSectionCovariantDerivative,hD,h0 x hx,map_zero,smul_zero,Finset.sum_const_zero,sub_zero]

lemma contDiffOn_gradedSphereSectionCovariantDerivative {Y : Set X} (hY : IsOpen Y)
    (s : ℝ) (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev s) (hU : ContDiffOn ℝ ∞ U Y) (a : X) :
    ContDiffOn ℝ ∞ (fun x => gradedSphereSectionCovariantDerivative s d U x a) Y := by
  have hD : ContDiffOn ℝ ∞ (fun x => fderiv ℝ U x a) Y :=
    (hU.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have hG (i j : I) := hg.contDiffOn_frameConnection hY hK d.frame he (fun _ => a) contDiffOn_const i j
  exact ((sphereSobolevInclusionL s (s-1) (by linarith)).contDiff.comp_contDiffOn hD).sub
    (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (contDiffOn_const.mul (hG i j)).smul ((sphereSobolevRotationL s i j).contDiff.comp_contDiffOn hU))))

theorem contDiff_supported_gradedSphereSectionCovariantDerivative {Y : Set X} (hY : IsOpen Y)
    (s : ℝ) (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev s) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) (a : X) :
    ContDiff ℝ ∞ (fun x => gradedSphereSectionCovariantDerivative s d U x a) ∧
      ∀ x ∉ S,gradedSphereSectionCovariantDerivative s d U x a=0 := by
  have hLocal := contDiffOn_gradedSphereSectionCovariantDerivative hY s d hg hK he U hU.contDiffOn a
  have hOff := gradedSphereSectionCovariantDerivative_zero_off s d U S hS h0 a
  exact ⟨contDiff_of_tsupport_subset hY _ hLocal ((tsupport_subset_of_zero_off _ S hS hOff).trans hSY),hOff⟩

end ShrinkingSpheres
