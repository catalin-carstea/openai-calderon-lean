import Proof.InverseEndpointCompatibility
import Proof.ScalarConjugationDefect
import Proof.SkewNegativeHalfCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma conjugation_taylor_kernel_endpoint_compatible {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : E →L[ℝ] F) (M C D : E →L[ℝ] E) (MN CN DN : F →L[ℝ] F) (r : ℝ)
    (hM : M.IsInvertible) (hMN : MN.IsInvertible)
    (hMI : I.comp M=MN.comp I) (hCI : I.comp C=CN.comp I) (hDI : I.comp D=DN.comp I) :
    I.comp (-M.inverse.comp C+r • D)=(-MN.inverse.comp CN+r • DN).comp I := by
  have hInv := inverse_endpoint_compatible I M MN hM hMN hMI
  apply ContinuousLinearMap.ext
  intro u
  have hi (v : E) : I (M.inverse v)=MN.inverse (I v) := DFunLike.congr_fun hInv v
  have hc : I (C u)=CN (I u) := DFunLike.congr_fun hCI u
  have hd : I (D u)=DN (I u) := DFunLike.congr_fun hDI u
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.neg_apply,_root_.smul_apply,
    map_add,map_neg,map_smul]
  rw [hi,hc,hd]

/-- A genuine high-to-negative realization of a skew kernel determines
    its positive-half realization through the physical inclusions. -/
lemma higher_negative_skew_kernel_half_compatible
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hHigh : (sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH=
      KN.comp (sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (hSkew : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))=
      KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hH := DFunLike.congr_fun hHigh u
  have hS := DFunLike.congr_fun hSkew (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at hH hS ⊢
  exact hH.trans hS.symm
end ShrinkingSpheres
