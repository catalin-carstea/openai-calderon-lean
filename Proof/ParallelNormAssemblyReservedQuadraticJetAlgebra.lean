import Proof.ParallelNormAssemblyReservedHigherBridge
import Proof.HalfFamilyDerivativeCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

def frameAngularConnectionNegativeHalfL (d : Data) (y a : X) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(3/2:ℝ)) :=
  ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL (-(1/2:ℝ)) i j

def quadraticOperatorCovariantDerivativeL (d : Data)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (y a : X) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (-(3/2:ℝ)) :=
  (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
      ((fderiv ℝ C y a).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))-
    (frameAngularConnectionNegativeHalfL d y a).comp
      ((C y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))+
    (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
      ((C y).comp (frameAngularConnectionFiveHalfL d y a))

lemma frame_connection_negative_half_compatible (d : Data) (y a : X) (u : SphereSobolev (1/2:ℝ)) :
    frameAngularConnectionNegativeHalfL d y a
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) u)=
      sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
        (frameAngularConnectionHalfL d y a u) := by
  simp only [frameAngularConnectionNegativeHalfL,frameAngularConnectionHalfL,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [sphereSobolevInclusionL,show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num,
    show (-(1/2:ℝ))-1= -(3/2:ℝ) by norm_num] using
    sphereSobolevRotationL_inclusion_apply (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) i j u

/-- Covariant product rule for two genuine order-one angular operators,
retaining the actual common higher first-word lift. It requires only FIRST
LOW and HIGH jets. Every negative output inclusion is explicit. -/
theorem quadratic_covariant_product_rule (d : Data)
    (L : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (LA H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (y a : X) (hL : ContDiffAt ℝ ∞ L y) (hH : ContDiffAt ℝ ∞ H y)
    (DL : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (DH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hBalanced : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (LA y)=
      (L y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hDL : halfOperatorCovariantDerivativeL d L LA y a=
      DL.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hDH : higherOperatorCovariantDerivativeL d H y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (DH.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))
    (u : SphereSobolev (5/2:ℝ)) (v : SphereSobolev (3/2:ℝ))
    (hv : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v=
      H y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) :
    quadraticOperatorCovariantDerivativeL d (fun x => (L x).comp (H x)) y a u=
      sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
        ((DL.comp (H y)+(L y).comp DH)
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) := by
  let Ineg := sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
  let Ihalf := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Ju := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
  have hProduct := ((hL.differentiableAt (by simp)).hasFDerivAt.clm_comp
    (hH.differentiableAt (by simp)).hasFDerivAt).fderiv
  have hD : fderiv ℝ (fun x => (L x).comp (H x)) y a=
      (L y).comp (fderiv ℝ H y a)+(fderiv ℝ L y a).comp (H y) := by
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply] using congrArg
        (fun A : X →L[ℝ] SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A a) hProduct
  have hLow := DFunLike.congr_fun hDL v
  simp only [halfOperatorCovariantDerivativeL] at hLow
  rw [directional_half_family_comp_fixed L hL a] at hLow
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,directionalFDeriv] at hLow
  rw [hv] at hLow
  have hBal := DFunLike.congr_fun hBalanced v
  simp only [ContinuousLinearMap.comp_apply] at hBal
  rw [hv] at hBal
  have hConn := (congrArg (frameAngularConnectionNegativeHalfL d y a) hBal).symm.trans
    (frame_connection_negative_half_compatible d y a (LA y v))
  have hHigh := DFunLike.congr_fun hDH u
  simp only [higherOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply] at hHigh
  have hRot := DFunLike.congr_fun (frameAngularConnectionHigherL_compatible d y a) v
  simp only [ContinuousLinearMap.comp_apply] at hRot
  rw [hv] at hRot
  have hHighHalf : (fderiv ℝ H y a) Ju-frameAngularConnectionHigherL d y a v+
      H y (frameAngularConnectionFiveHalfL d y a u)=DH Ju := by
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    simp only [map_add,map_sub]
    rw [←hRot] at hHigh
    exact hHigh
  have hLowN := congrArg Ineg hLow
  have hHighN := congrArg (fun z => Ineg (L y z)) hHighHalf
  simp only [map_add,map_sub] at hLowN hHighN
  have hSum := congrArg₂ (fun x z : SphereSobolev (-(3/2:ℝ)) => x+z) hLowN hHighN
  simp only [quadraticOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,_root_.add_apply,
    _root_.sub_apply,hD,map_add,map_sub]
  rw [hConn]
  change Ineg (L y ((fderiv ℝ H y a) Ju))+Ineg ((fderiv ℝ L y a) (H y Ju))-
    Ineg (frameAngularConnectionHalfL d y a (LA y v))+
    Ineg (L y (H y (frameAngularConnectionFiveHalfL d y a u)))=
    Ineg (DL (H y Ju))+Ineg (L y (DH Ju))
  convert hSum using 1 <;> abel

end ShrinkingSpheres.ParallelEnergy
