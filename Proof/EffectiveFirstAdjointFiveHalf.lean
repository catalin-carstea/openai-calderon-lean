import Proof.FullFirstAdjointFiveHalf
import Proof.FirstCovariantCoordinateAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma balanced_real_scalar_sub {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I0 T C : E →L[ℝ] E) (J A K : H →L[ℝ] E) (w : ℝ)
    (hT : T.adjoint=T) (hA : I0.comp A=C.adjoint.comp J) (hK : I0.comp K=T.comp J) :
    I0.comp (A-w • K)=(C-w • T).adjoint.comp J := by
  rw [map_sub,map_smul,hT,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp,hA,hK]

lemma PhysicalPrincipalData.firstDerivativeAdjointFiveHalfL_balanced
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (j : I) :
    (sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeAdjointFiveHalfL W j)=
      (P.firstDerivativeHalfL y j).adjoint.comp
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hR (i : I) : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (W.adjointHigh (.inr (.inl i)))=(flatHalfRaisingL i).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := W.adjoint_compatible (.inr (.inl i))
  have hE (i : I) : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (W.adjointHigh (.inr (.inr i)))=(P.first.low i y).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := W.adjoint_compatible (.inr (.inr i))
  have hMid := P.firstDerivativeAdjointHigherFamily_balanced
    (fun i => W.adjointHigh (.inr (.inl i))) (fun i _ => W.adjointHigh (.inr (.inr i))) y hR hE j
  have hTop := P.firstDerivativeAdjointFiveHalfL_inclusion hy W j
  apply ContinuousLinearMap.ext
  intro u
  have hm := DFunLike.congr_fun hMid (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
  have ht := DFunLike.congr_fun hTop u
  simp only [ContinuousLinearMap.comp_apply] at hm ht
  calc
    _ = sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
          (P.firstDerivativeAdjointFiveHalfL W j u)) :=
      (sphereSobolevInclusionL_trans_apply _ _ _ _ _ _).symm
    _ = _ := (congrArg (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) ht).trans
      (hm.trans (by simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply]))

def PhysicalPrincipalData.firstCoordinateAdjointFiveHalfL
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (W : PhysicalPotentialQuarticData P y CG CK) (b : I) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  ∑ j : I,d.frame y j b • P.firstDerivativeAdjointFiveHalfL W j

lemma PhysicalPrincipalData.firstCoordinateAdjointFiveHalfL_balanced
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (b : I) :
    (sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstCoordinateAdjointFiveHalfL W b)=
      (P.firstDerivativeCoordinateHalfL y b).adjoint.comp
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  finite_real_adjoint_balanced_combination _ _ (fun j => P.firstDerivativeHalfL y j)
    (fun j => P.firstDerivativeAdjointFiveHalfL W j)
    (fun j => P.firstDerivativeAdjointFiveHalfL_balanced hy W j) (fun j => d.frame y j b)

def PhysicalPrincipalData.firstCovariantCoordinateAdjointFiveHalfL
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (W : PhysicalPotentialQuarticData P y CG CK) (b : I) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  P.firstCoordinateAdjointFiveHalfL W b-scalarPrincipalConnectionWeight d b y •
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)

lemma PhysicalPrincipalData.firstCovariantCoordinateAdjointFiveHalfL_balanced
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (b : I) :
    (sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstCovariantCoordinateAdjointFiveHalfL W b)=
      (P.firstCovariantCoordinateHalfL b y).adjoint.comp
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hK : (sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply]
  exact balanced_real_scalar_sub (E:=SphereSobolev (1/2:ℝ)) (H:=SphereSobolev (5/2:ℝ))
    _ _ _ _ _ _ _ sphereSobolevHalfNegativeInclusion_adjoint
    (P.firstCoordinateAdjointFiveHalfL_balanced hy W b) hK

/-- The high constructed core agrees with ANY already selected genuine
effective adjoint family through the actual inclusion. -/
lemma PhysicalPrincipalData.firstCovariantCoordinateAdjointFiveHalfL_inclusion
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (b : I)
    (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp A=
      (P.firstCovariantCoordinateHalfL b y).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (P.firstCovariantCoordinateAdjointFiveHalfL W b)=
      A.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have ht := DFunLike.congr_fun (P.firstCovariantCoordinateAdjointFiveHalfL_balanced hy W b) u
  have ha := DFunLike.congr_fun hA (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at ht ha ⊢
  exact ht.trans ha.symm

end ShrinkingSpheres
