import Proof.CompleteAdjointProductExpansion
import Proof.ActualFrameCorrectionCrossBudget
import Proof.ActualRaisingCorrectionMatrixBudget
import Proof.ActualDegreeCorrectionMatrixBudget
import Proof.ActualFrameMatrixRaisingCrossBudget
import Proof.ActualFrameMatrixDegreeCrossBudget
import Proof.ActualFrameErrorProductBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def principalLeadingAdjointProductValue (d : Data) (y : X) (u : SphereSobolev 2) : SphereSobolev 0 :=
  d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
    actualLeadingFrameAdjointL d i y
      ((d.radius y)⁻¹ • flatTwoRaisingL j u+
        (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)) • sphereSobolevShiftedDegreeL 2 u))

namespace SecondTraceSectionOutput
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {φ : Field} {L : ℂ →L[ℝ] ℝ} {F : X × X → ℝ} {hF : ContDiff ℝ ∞ F}

/-- Every actual principal zero-base adjoint product is identified on one
    shared canonical input. The only unbounded leading part is explicit;
    every remaining group is the already controlled actual coefficient. -/
lemma principal_adjoint_product_balanced (P : SecondTraceSectionOutput Y d A G S φ L F hF)
    {CE : ℝ} (E : ActualFrameErrorEndpointPair Y d A G CE) {y : X} (hy : y ∈ Y)
    (hr : d.radius y ≠ 0) :
    let u := ambientSobolevSection 2 (by norm_num) F hF y
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
        completeFirstAdjointFamily d A G i y
          (ambientSobolevSection 1 (by norm_num) (P.representative j) (P.smooth j) y)))=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (principalLeadingAdjointProductValue d y u)+
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (principalRaisingCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) u))+
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (principalDegreeCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) u))+
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (principalCorrectionProductL 0 d y (sphereSobolevInclusionL 2 0 (by norm_num) u))+
      E.principalRaisingCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
      E.principalDegreeCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
      E.principalCorrectionCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
      E.radiusPrincipalProductL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  dsimp only
  let u := ambientSobolevSection 2 (by norm_num) F hF y
  let v := fun j => ambientSobolevSection 1 (by norm_num) (P.representative j) (P.smooth j) y
  let e := P.errorLift y
  let r := d.radius y
  let b := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  let q := fun i j => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j
  let W := fun j => firstFrameAdjointCorrectionSobolevL d y j (sphereSobolevInclusionL 2 1 (by norm_num) u)
  let Ei := fun i => actualFrameFirstAdjointErrorFamily d A G i y
  let Sum := fun R : I → I → SphereSobolev 0 => ∑ i : I,∑ j : I,q i j • R i j
  let Model := fun i j => r • actualLeadingFrameAdjointL d i y
    (r⁻¹ • flatTwoRaisingL j u+b j • sphereSobolevShiftedDegreeL 2 u)
  let RF := fun i j => flatOneRaisingL i (W j)+firstFrameAdjointCorrectionL d y i
    (flatOneRaisingL j (sphereSobolevInclusionL 2 1 (by norm_num) u))
  let DF := fun i j => (r*b i) • sphereSobolevDegreeL (W j)+(r*b j) •
    firstFrameAdjointCorrectionL d y i (sphereSobolevDegreeL (sphereSobolevInclusionL 2 1 (by norm_num) u))
  let FF := fun i j => r • firstFrameAdjointCorrectionL d y i (sphereSobolevInclusionL 1 0 (by norm_num) (W j))
  let RE := fun i j => flatOneRaisingL i (e j)+Ei i (flatTwoRaisingL j u)
  let DE := fun i j => (r*b i) • sphereSobolevDegreeL (e j)+(r*b j) • Ei i (sphereSobolevShiftedDegreeL 2 u)
  let FE := fun i j => r • (firstFrameAdjointCorrectionL d y i (sphereSobolevInclusionL 1 0 (by norm_num) (e j))+Ei i (W j))
  let EE := fun i j => r • Ei i (e j)
  have hs (R : I → I → SphereSobolev 0) : r • Sum R=Sum (fun i j => r • R i j) := by
    dsimp only [Sum]
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm r (q i j) (R i j)
  have hPoint (i j : I) : r • completeFirstAdjointFamily d A G i y (v j)=
      Model i j+RF i j+DF i j+FF i j+RE i j+DE i j+FE i j+EE i j :=
    complete_first_adjoint_product_expansion d A G y hr i j u (v j)
  have hSum : Sum (fun i j => r • completeFirstAdjointFamily d A G i y (v j))=
      Sum Model+Sum RF+Sum DF+Sum FF+Sum RE+Sum DE+Sum FE+Sum EE := by
    calc
      _ = Sum (fun i j => Model i j+RF i j+DF i j+FF i j+RE i j+DE i j+FE i j+EE i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun z : SphereSobolev 0 => q i j • z) (hPoint i j)
      _ = _ := by simp only [Sum,smul_add,Finset.sum_add_distrib]
  have hValue := (hs (fun i j => completeFirstAdjointFamily d A G i y (v j))).trans hSum
  let Inc := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  have hModel : Sum Model=principalLeadingAdjointProductValue d y u :=
    (hs (fun i j => actualLeadingFrameAdjointL d i y
      (r⁻¹ • flatTwoRaisingL j u+b j • sphereSobolevShiftedDegreeL 2 u))).symm
  have hRF : Sum RF=principalRaisingCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) u) := by
    simp only [Sum,RF,principalRaisingCorrectionCrossL,firstCorrectionMatrixCrossL,
      _root_.sum_apply,_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.comp_apply,flatOneRaisingL,q,W]
  have hDF : Sum DF=principalDegreeCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) u) :=
    principalDegreeCorrectionCrossL_actual d y (sphereSobolevInclusionL 2 1 (by norm_num) u)
  have hFF : Sum FF=principalCorrectionProductL 0 d y (sphereSobolevInclusionL 2 0 (by norm_num) u) := by
    exact (hs (fun i j => firstFrameAdjointCorrectionL d y i
      (sphereSobolevInclusionL 1 0 (by norm_num) (W j)))).symm.trans
        (principalCorrectionProductL_actual d y u)
  have hRE : Inc (Sum RE)=E.principalRaisingCrossL y
      (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) :=
    P.principal_raising_cross_actual E hy
  have hDE : Inc (Sum DE)=E.principalDegreeCrossL y
      (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) :=
    P.principal_degree_cross_actual E hy
  have hFE : Inc (Sum FE)=E.principalCorrectionCrossL y
      (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
    exact (congrArg Inc (hs (fun i j => firstFrameAdjointCorrectionL d y i
      (sphereSobolevInclusionL 1 0 (by norm_num) (e j))+Ei i (W j))).symm).trans
        (P.principal_correction_cross_actual E hy)
  have hEE : Inc (Sum EE)=E.radiusPrincipalProductL y
      (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
    exact (congrArg Inc (hs (fun i j => Ei i (e j))).symm).trans
      (P.radius_error_product_actual E hy)
  have hMap := congrArg Inc hValue
  simp only [map_add] at hMap
  have hadd {a b c d : SphereSobolev (-(1/2:ℝ))} (hab : a=b) (hcd : c=d) : a+c=b+d :=
    congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => x+y) hab hcd
  exact hMap.trans
    (hadd (hadd (hadd (hadd (hadd (hadd (hadd (congrArg Inc hModel) (congrArg Inc hRF))
      (congrArg Inc hDF)) (congrArg Inc hFF)) hRE) hDE) hFE) hEE)
end SecondTraceSectionOutput
end ShrinkingSpheres
