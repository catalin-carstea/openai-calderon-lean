import Proof.CovariantHalfCoarseBridge
import Proof.CanonicalHorizontalSection
import Proof.CanonicalTestSobolevSections
import Proof.AngularComponentData
import Proof.PartialEnergyBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def halfSectionCovariantDerivativeL (d : Data) (U : X → SphereSobolev (3/2:ℝ)) (y : X) :
    X →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (fderiv ℝ U y)-
    ∑ i : I,∑ j : I,((1/2:ℝ) • frameConnectionLinear d.γ d.frame y i j).smulRight
      (sphereSobolevRotationL (3/2:ℝ) i j (U y))

lemma halfSectionCovariantDerivativeL_apply (d : Data) (U : X → SphereSobolev (3/2:ℝ)) (y a : X) :
    halfSectionCovariantDerivativeL d U y a=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fderiv ℝ U y a)-
        frameAngularConnectionHigherL d y a (U y) := by
  simp only [halfSectionCovariantDerivativeL,frameAngularConnectionHigherL,_root_.sub_apply,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
    frameConnectionLinear_apply,smul_eq_mul]

lemma canonical_half_covariant_section_eq (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y a : X) :
    halfSectionCovariantDerivativeL d (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG) y a=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (highSectionCovariantDerivative d (ambientSobolevSection 2 (by norm_num) G hG) y a) := by
  let U2 := ambientSobolevSection 2 (by norm_num) G hG
  let UH := ambientSobolevSection (3/2:ℝ) (by norm_num) G hG
  let I2 := sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)
  have hI : (fun x => I2 (U2 x))=UH := funext (ambientSobolevSection_inclusion 2 (3/2:ℝ)
    (by norm_num) (by norm_num) (by norm_num) G hG)
  have hU := (contDiff_ambientSobolevSection 2 (by norm_num) G hG).differentiable (by simp) y
  have hD := I2.hasFDerivAt.comp y hU.hasFDerivAt
  change HasFDerivAt (fun x => I2 (U2 x)) (I2.comp (fderiv ℝ U2 y)) y at hD
  rw [hI] at hD
  have hFD : fderiv ℝ UH y a=I2 (fderiv ℝ U2 y a) := DFunLike.congr_fun hD.fderiv a
  rw [halfSectionCovariantDerivativeL_apply]
  change sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fderiv ℝ UH y a)-
    frameAngularConnectionHigherL d y a (UH y)=_
  rw [hFD,← congrFun hI y]
  change sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (I2 (fderiv ℝ U2 y a))-
    frameAngularConnectionHigherL d y a (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U2 y))=_
  rw [frameAngularConnectionHigherL_upper_core]
  simp only [I2,U2,highSectionCovariantDerivative,sphereSobolevInclusionL_trans_apply,map_sub,map_sum,map_smul]

namespace AngularComponentData
variable {Y : Set X} {d : Data} {φ : Field} {L : ℂ →L[ℝ] ℝ}
  {E : HarmonicTestExpansion Y d.γ d.frame φ}

/-- The genuine covariant half derivative in the Green identity is the
    SAME already selected physical horizontal representative. -/
theorem half_covariant_section_eq (Q : AngularComponentData E d.radius L)
    (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) (i : I) :
    halfSectionCovariantDerivativeL d
      (ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth)) y (d.frame y i)=
      ambientSobolevSection (1/2:ℝ) (by norm_num) (Q.horizontalRepresentative i) (Q.horizontalSmooth i) y := by
  rw [canonical_half_covariant_section_eq]
  rw [canonical_horizontal_oneSection_eq hY d hg hK he hFrame φ hφ L
    (fun p => L (E.representative p)) (Q.horizontalRepresentative i)
    (L.contDiff.comp E.representativeSmooth) (Q.horizontalSmooth i) i
    (fun x hx w => congrArg L (E.representativeEq x hx w)) (Q.horizontalEq i) hy]
  exact ambientSobolevSection_inclusion 1 (1/2:ℝ) (by norm_num) (by norm_num) (by norm_num) _ _ y

lemma norm_half_covariant_section (Q : AngularComponentData E d.radius L)
    (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) (i : I) :
    ‖halfSectionCovariantDerivativeL d
      (ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth)) y (d.frame y i)‖=
      ‖Q.horizontalBessel i (1/2:ℝ) (by norm_num) y‖ := by
  rw [Q.half_covariant_section_eq hY hg hK he hFrame hφ hy i,norm_ambientSobolevSection]
  rfl
end AngularComponentData
end ShrinkingSpheres
