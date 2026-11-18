import Proof.HalfCovariantSmallScalarProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma half_covariant_sub (d : Data)
    (C F : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H G : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hF : ContDiffAt ℝ ∞ F y) :
    halfOperatorCovariantDerivativeL d (fun x => C x-F x) (fun x => H x-G x) y a=
      halfOperatorCovariantDerivativeL d C H y a-halfOperatorCovariantDerivativeL d F G y a := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hFun : (fun x => (C x-F x).comp J)=(fun x => (C x).comp J-(F x).comp J) := by
    funext x
    exact ContinuousLinearMap.sub_comp _ _ _
  have hD : directionalFDeriv a (fun x => (C x-F x).comp J) y=
      directionalFDeriv a (fun x => (C x).comp J) y-directionalFDeriv a (fun x => (F x).comp J) y := by
    rw [hFun]
    unfold directionalFDeriv
    rw [fderiv_fun_sub ((hC.clm_comp contDiffAt_const).differentiableAt (by simp))
      ((hF.clm_comp contDiffAt_const).differentiableAt (by simp))]
    rfl
  unfold halfOperatorCovariantDerivativeL
  rw [hD]
  apply ContinuousLinearMap.ext
  intro u
  simp only [J,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,map_add,map_sub]
  abel

lemma half_covariant_inclusion_zero (d : Data) (y a : X) :
    halfOperatorCovariantDerivativeL d
      (fun _ => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (fun _ => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) y a=0 := by
  unfold halfOperatorCovariantDerivativeL
  simp only [directionalFDeriv,fderiv_const_apply,_root_.zero_apply,zero_sub]
  rw [frameAngularConnectionHigherL_compatible d y a]
  abel

lemma half_covariant_scalar_inclusion_higher (d : Data) (w : X → ℝ) (y a : X)
    (hw : ContDiffAt ℝ ∞ w y) :
    halfOperatorCovariantDerivativeL d
      (fun x => w x • sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (fun x => w x • sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (directionalFDeriv a w y • sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [halfOperatorCovariantDerivativeL_smul d w
    (fun _ => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (fun _ => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) y a hw contDiffAt_const,
    half_covariant_inclusion_zero d y a]
  simp only [smul_zero,add_zero,ContinuousLinearMap.comp_smul]

lemma norm_scalar_higher_inclusion_le (a : ℝ) :
    ‖a • sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)‖ ≤ |a| := by
  rw [norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (abs_nonneg a)).trans_eq (mul_one _)

end ShrinkingSpheres.ParallelEnergy
