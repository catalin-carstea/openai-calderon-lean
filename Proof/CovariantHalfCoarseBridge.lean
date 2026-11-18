import Proof.CovariantHalfOperatorGreen
import Proof.EndpointCompatibleDerivative
import Proof.ActualCovariantRotationGraph
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma frameAngularConnectionHalfL_lower_coarse (d : Data) (y a : X) (v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (-(1/2:ℝ)) (-1) (by norm_num) (frameAngularConnectionHalfL d y a v)=
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        sphereSobolevRotationL 0 i j (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) v) := by
  simp only [frameAngularConnectionHalfL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [sphereSobolevInclusionL,show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num,
    show (0:ℝ)-1= -1 by norm_num] using
    (sphereSobolevRotationL_inclusion_apply (1/2:ℝ) 0 (by norm_num) i j v).symm

lemma frameAngularConnectionHigherL_upper_core (d : Data) (y a : X) (u : SphereSobolev 2) :
    frameAngularConnectionHigherL d y a (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL 2 i j u) := by
  simp only [frameAngularConnectionHigherL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [sphereSobolevInclusionL,show (2:ℝ)-1=1 by norm_num,
    show (3/2:ℝ)-1=1/2 by norm_num] using
    sphereSobolevRotationL_inclusion_apply 2 (3/2:ℝ) (by norm_num) i j u

/-- The literal covariant derivative used by the Green formula is the SAME
    physical coarse covariant jet, restricted through genuine inclusions.
    Only actual family germs and endpoint identities are used. -/
theorem halfOperatorCovariantDerivativeL_eq_coarse {d : Data} {y a : X}
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hH : DifferentiableAt ℝ H y) (hC : DifferentiableAt ℝ C y)
    (hLow : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (H x)=
      (C x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hHigh : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Ch y)=
      (H y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hGraph : CoarseCovariantRotationGraph d y a H S) :
    halfOperatorCovariantDerivativeL d C Ch y a=
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hProd := hC.hasFDerivAt.clm_comp (hasFDerivAt_const J y)
  have hCd : directionalFDeriv a (fun x => (C x).comp J) y=(fderiv ℝ C y a).comp J := by
    have hh := DFunLike.congr_fun hProd.fderiv a
    simpa only [directionalFDeriv,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      _root_.zero_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.compL_apply] using hh
  have hDeriv := compatible_endpoint_fderiv H C
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) y a hH hC hLow
  have hLowAt := hLow.self_of_nhds
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (-(1/2:ℝ)) (-1) (by norm_num)
  have hD : sphereSobolevInclusionL (-(1/2:ℝ)) (-1) (by norm_num)
      (directionalFDeriv a (fun x => (C x).comp J) y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u))=
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (fderiv ℝ H y a (sphereSobolevInclusionL 2 1 (by norm_num) u)) := by
    rw [hCd]
    have hh := congrArg (sphereSobolevInclusionL (-(1/2:ℝ)) (-1) (by norm_num))
      (DFunLike.congr_fun hDeriv (sphereSobolevInclusionL 2 1 (by norm_num) u))
    simpa only [J,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh.symm
  have hConn1 : sphereSobolevInclusionL (-(1/2:ℝ)) (-1) (by norm_num)
      (frameAngularConnectionHalfL d y a (Ch y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)))=
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        sphereSobolevRotationL 0 i j (H y (sphereSobolevInclusionL 2 1 (by norm_num) u)) := by
    rw [frameAngularConnectionHalfL_lower_coarse]
    have hh := DFunLike.congr_fun hHigh (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)
    simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at hh
    rw [hh]
  have hConn2 : sphereSobolevInclusionL (-(1/2:ℝ)) (-1) (by norm_num)
      (C y (frameAngularConnectionHigherL d y a (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)))=
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        sphereSobolevInclusionL 0 (-1) (by norm_num) (H y (sphereSobolevRotationL 2 i j u)) := by
    rw [frameAngularConnectionHigherL_upper_core]
    have hh := congrArg (sphereSobolevInclusionL (-(1/2:ℝ)) (-1) (by norm_num))
      (DFunLike.congr_fun hLowAt (∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL 2 i j u))
    simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply,map_sum,map_smul] using hh.symm
  simp only [ContinuousLinearMap.comp_apply,halfOperatorCovariantDerivativeL,
    _root_.add_apply,_root_.sub_apply,map_add,map_sub,sphereSobolevInclusionL_trans_apply]
  rw [hD,hConn1,hConn2,hGraph u]
  simp only [smul_sub,Finset.sum_sub_distrib]
  abel
end ShrinkingSpheres
