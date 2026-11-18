import Proof.CovariantRotationGraphOperations
import Proof.CoarseCovariantJetFamily
import Proof.OneSectionCovariantDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarse_covariant_inclusion_graph (d : Data) (y a : X) :
    CoarseCovariantRotationGraph d y a
      (fun _ => sphereSobolevInclusionL 1 0 (by norm_num)) 0 := by
  intro u
  have hD : fderiv ℝ (fun _ : X => sphereSobolevInclusionL 1 0 (by norm_num)) y=0 :=
    (hasFDerivAt_const (sphereSobolevInclusionL 1 0 (by norm_num)) y).fderiv
  rw [hD]
  simp only [_root_.zero_apply,map_zero,
    sphereSobolevRotationL_zero_inclusion_one,sphereSobolevRotationL_one_inclusion_two,
    sub_self,smul_zero,Finset.sum_const_zero]

/-- A real scalar multiple of the genuine inclusion has precisely its
ordinary scalar derivative as its covariant jet. -/
lemma coarse_covariant_scalar_inclusion_graph (d : Data) (w : X → ℝ) (y a : X)
    (hw : DifferentiableAt ℝ w y) :
    CoarseCovariantRotationGraph d y a (fun x => w x • sphereSobolevInclusionL 1 0 (by norm_num))
      (fderiv ℝ w y a • sphereSobolevInclusionL 1 0 (by norm_num)) := by
  simpa only [smul_zero,zero_add] using
    (coarse_covariant_inclusion_graph d y a).smul w hw (differentiableAt_const _)

lemma coarse_covariant_scalar_inclusion_two_jets (d : Data) (w : X → ℝ) (y : X) (i j : I)
    (hw : ContDiffAt ℝ ∞ w y) :
    CoarseCovariantRotationGraph d y (axis i) (fun x => w x • sphereSobolevInclusionL 1 0 (by norm_num))
      (coordDeriv i w y • sphereSobolevInclusionL 1 0 (by norm_num)) ∧
    CoarseCovariantRotationGraph d y (axis j)
      (fun x => coordDeriv i w x • sphereSobolevInclusionL 1 0 (by norm_num))
      (coordDeriv j (coordDeriv i w) y • sphereSobolevInclusionL 1 0 (by norm_num)) := by
  refine ⟨coarse_covariant_scalar_inclusion_graph d w y (axis i) (hw.differentiableAt (by simp)),?_⟩
  exact coarse_covariant_scalar_inclusion_graph d (coordDeriv i w) y (axis j)
    (((hw.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp))

lemma norm_scalar_coarse_inclusion_le (w : ℝ) :
    ‖w • sphereSobolevInclusionL 1 0 (by norm_num)‖ ≤ |w| := by
  rw [norm_smul,Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le 1 0 (by norm_num)) (abs_nonneg w)

end ShrinkingSpheres
