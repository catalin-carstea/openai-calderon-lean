import Proof.ActualCovariantRotationGraph
import Proof.RightMultiplierRotationGraph
import Proof.RadialCorrectionFrameCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevRotationL_zero_inclusion_one (i j : I) (u : SphereSobolev 1) :
    sphereSobolevRotationL 0 i j (sphereSobolevInclusionL 1 0 (by norm_num) u)=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) (sphereSobolevRotationL 1 i j u) := by
  simpa only [sphereSobolevInclusionL,show (1:ℝ)-1=0 by norm_num,show (0:ℝ)-1= -1 by norm_num] using
    sphereSobolevRotationL_inclusion_apply 1 0 (by norm_num) i j u

/-- An order-zero operator with its genuine H1 realization gives a coarse
    covariant graph directly from its exact horizontal commutator. -/
lemma coarseCovariantRotationGraph_of_orderZero (d : Data) (y a : X)
    (B0 : X → SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (B1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (hB : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (B1 u)=
      B0 y (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (hD : DifferentiableAt ℝ B0 y) :
    CoarseCovariantRotationGraph d y a
      (fun x => (B0 x).comp (sphereSobolevInclusionL 1 0 (by norm_num)))
      ((fderiv ℝ B0 y a).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
        (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)).comp B1-
        (B0 y).comp (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a))) := by
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hProduct := hD.hasFDerivAt.clm_comp (hasFDerivAt_const I10 y)
  have hDF : fderiv ℝ (fun x => (B0 x).comp I10) y a=(fderiv ℝ B0 y a).comp I10 := by
    have hh := DFunLike.congr_fun hProduct.fderiv a
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      _root_.zero_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.compL_apply] using hh
  intro u
  have hRot (i j : I) :
      sphereSobolevRotationL 0 i j (B0 y (I10 (sphereSobolevInclusionL 2 1 (by norm_num) u)))=
        sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num)
          (sphereSobolevRotationL 1 i j (B1 (sphereSobolevInclusionL 2 1 (by norm_num) u))) := by
    rw [← hB,sphereSobolevRotationL_zero_inclusion_one]
  change sphereSobolevInclusionL 0 (-1) (by norm_num)
      (((fderiv ℝ B0 y a).comp I10+(angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)).comp B1-
        (B0 y).comp (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)))
          (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
    sphereSobolevInclusionL 0 (-1) (by norm_num)
      (fderiv ℝ (fun x => (B0 x).comp I10) y a (sphereSobolevInclusionL 2 1 (by norm_num) u))-
    ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
      (sphereSobolevRotationL 0 i j (B0 y (I10 (sphereSobolevInclusionL 2 1 (by norm_num) u)))-
        sphereSobolevInclusionL 0 (-1) (by norm_num) (B0 y (I10 (sphereSobolevRotationL 2 i j u))))
  rw [hDF]
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,hRot,
    angularConnectionL,_root_.sum_apply,_root_.smul_apply,map_add,map_sub,map_sum,map_smul,
    sphereSobolevRotationL_one_inclusion_two,neg_mul,neg_smul,Finset.sum_neg_distrib,smul_sub,_root_.neg_apply,map_neg]
  simp only [I10,Fin.sum_univ_three]
  module
end ShrinkingSpheres
