import Proof.HighSectionCovariantDerivativeLinear
import Proof.SecondTraceSectionExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma oneSectionCovariantDerivative_smul (d : Data) (w : X → ℝ) (U : X → SphereSobolev 1)
    (y a : X) (hw : DifferentiableAt ℝ w y) (hU : DifferentiableAt ℝ U y) :
    oneSectionCovariantDerivative d (fun x => w x • U x) y a=
      fderiv ℝ w y a • sphereSobolevInclusionL 1 0 (by norm_num) (U y)+
        w y • oneSectionCovariantDerivative d U y a := by
  rw [oneSectionCovariantDerivative,fderiv_fun_smul hw hU]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,_root_.smul_apply,
    map_add,map_smul,smul_add,oneSectionCovariantDerivative,smul_sub,Finset.smul_sum,smul_smul]
  simp only [mul_comm]
  abel

lemma highSectionCovariantDerivative_smul (d : Data) (w : X → ℝ) (U : X → SphereSobolev 2)
    (y a : X) (hw : DifferentiableAt ℝ w y) (hU : DifferentiableAt ℝ U y) :
    highSectionCovariantDerivative d (fun x => w x • U x) y a=
      fderiv ℝ w y a • sphereSobolevInclusionL 2 1 (by norm_num) (U y)+
        w y • highSectionCovariantDerivative d U y a := by
  rw [highSectionCovariantDerivative,fderiv_fun_smul hw hU]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,_root_.smul_apply,
    map_add,map_smul,smul_add,highSectionCovariantDerivative,smul_sub,Finset.smul_sum,smul_smul]
  simp only [mul_comm]
  abel

lemma contDiffOn_highSectionCovariantDerivative {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y) (a : X) :
    ContDiffOn ℝ ∞ (fun x => highSectionCovariantDerivative d U x a) Y := by
  simpa only [highSectionCovariantDerivativeLinear_apply] using
    (contDiffOn_highSectionCovariantDerivativeLinear hY d hg hK he U hU).clm_apply
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => a) Y)

/-- The actual second covariant section derivative has the scalar product
rule on the genuine H2/H1/H0 ladder. -/
theorem secondSectionCovariantDerivative_smul {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (w : X → ℝ) (hw : ContDiffOn ℝ ∞ w Y)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) (a b : X) :
    oneSectionCovariantDerivative d
      (fun x => highSectionCovariantDerivative d (fun z => w z • U z) x b) y a=
    fderiv ℝ (fun x => fderiv ℝ w x b) y a •
        sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
      fderiv ℝ w y b • sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y a)+
      fderiv ℝ w y a • sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y b)+
      w y • oneSectionCovariantDerivative d (fun x => highSectionCovariantDerivative d U x b) y a := by
  have hWD (x : X) (hx : x ∈ Y) := (hw.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  have hUD (x : X) (hx : x ∈ Y) := (hU.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  have hWb : ContDiffOn ℝ ∞ (fun x => fderiv ℝ w x b) Y :=
    (hw.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have hIUS : ContDiffOn ℝ ∞ (fun x => sphereSobolevInclusionL 2 1 (by norm_num) (U x)) Y :=
    (sphereSobolevInclusionL 2 1 (by norm_num)).contDiff.comp_contDiffOn hU
  have hDU := contDiffOn_highSectionCovariantDerivative hY d hg hK he U hU b
  have hG : (fun x => highSectionCovariantDerivative d (fun z => w z • U z) x b) =ᶠ[nhds y]
      (fun x => fderiv ℝ w x b • sphereSobolevInclusionL 2 1 (by norm_num) (U x)+
        w x • highSectionCovariantDerivative d U x b) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact highSectionCovariantDerivative_smul d w U x b (hWD x hx) (hUD x hx)
  have hF1 : DifferentiableAt ℝ (fun x => fderiv ℝ w x b •
      sphereSobolevInclusionL 2 1 (by norm_num) (U x)) y :=
    ((hWb.smul hIUS).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hF2 : DifferentiableAt ℝ (fun x => w x • highSectionCovariantDerivative d U x b) y :=
    ((hw.smul hDU).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  rw [oneSectionCovariantDerivative_congr_germ hG,
    oneSectionCovariantDerivative_add d
      (fun x => fderiv ℝ w x b • sphereSobolevInclusionL 2 1 (by norm_num) (U x))
      (fun x => w x • highSectionCovariantDerivative d U x b) y a hF1 hF2,
    oneSectionCovariantDerivative_smul d _ _ y a
      ((hWb.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      ((hIUS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)),
    oneSectionCovariantDerivative_smul d _ _ y a (hWD y hy)
      ((hDU.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)),
    oneSectionCovariantDerivative_high_inclusion d U y a (hUD y hy)]
  abel

end ShrinkingSpheres
