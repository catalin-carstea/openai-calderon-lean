import Proof.PhysicalPotentialCoreNormIdentity
import Proof.HalfDegreeGraphCoreLift
import Proof.DegreeAdjointHigherEndpoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SphereHarmonic.DegreeGraphLifting

lemma shiftedDegreeFiveHalf_inclusion (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (sphereSobolevShiftedDegreeL (5/2:ℝ) u)=
      sphereSobolevShiftedDegreeL (3/2:ℝ)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  have h := sphereSobolevShiftedDegreeL_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) u
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at h
  exact h

namespace PhysicalPotentialQuarticData
variable {Y : Set X} {d : Data} {CF CT CG CK : ℝ} {P : PhysicalPrincipalData Y d CF CT} {y : X}

lemma adjointHigh_degree (W : PhysicalPotentialQuarticData P y CG CK) (hy : y ∈ Y) :
    W.adjointHigh (.inl ())=P.potentialGeneratorHigh y (.inl ()) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hW := DFunLike.congr_fun (W.adjoint_compatible (.inl ())) u
  have hG := DFunLike.congr_fun (P.potential_generator_balanced hy (.inl ())) u
  simp only [ContinuousLinearMap.comp_apply,PhysicalPrincipalData.potentialGeneratorLow,
    sphereSobolevShiftedDegreeHalf_adjoint] at hW hG
  exact hW.trans hG.symm

def forwardFirstWordHigherL (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (sphereSobolevBesselOrderL (1/2:ℝ) (3/2:ℝ)).comp
    ((W.commHigh (.inl ()) a).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))+
      (P.potentialGeneratorHigh y a).comp (sphereSobolevShiftedDegreeL (5/2:ℝ))+
      (P.potentialGeneratorHigh y a).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))

def reverseFirstWordHigherL (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (sphereSobolevBesselOrderL (1/2:ℝ) (3/2:ℝ)).comp
    ((W.adjointHigh a).comp (sphereSobolevShiftedDegreeL (5/2:ℝ))-
      (W.commHigh a (.inl ())).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))+
      (W.adjointHigh a).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))

/-- The degree row of the SAME mixed commutator package supplies genuine
higher lifts of all first words. No invariant core or regularity premise is
assumed, and equality of Sobolev carrier types is never used as a graph. -/
lemma forwardFirstWordHigherL_inclusion (W : PhysicalPotentialQuarticData P y CG CK) (hy : y ∈ Y)
    (a : PhysicalPotentialGeneratorIndex) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (W.forwardFirstWordHigherL a u)=
      P.potentialGeneratorHigh y a (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  let U := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
  let D := sphereSobolevShiftedDegreeL (5/2:ℝ) u
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hC := DFunLike.congr_fun (W.commutator_compatible (.inl ()) a) U
  have hA := DFunLike.congr_fun (P.potential_generator_balanced hy a) D
  have hDU : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) D=
      P.potentialGeneratorHigh y (.inl ()) U := shiftedDegreeFiveHalf_inclusion u
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply] at hC hA
  rw [W.adjointHigh_degree hy] at hC
  rw [hDU] at hA
  have hC' : sphereSobolevShiftedDegreeL (1/2:ℝ) (P.potentialGeneratorHigh y a U)-
      J (P.potentialGeneratorHigh y a D)=J (W.commHigh (.inl ()) a U) := by
    rw [hA]
    simpa only [PhysicalPrincipalData.potentialGeneratorLow,sphereSobolevShiftedDegreeHalf_adjoint] using hC
  have hDeg : sphereSobolevShiftedDegreeL (1/2:ℝ) (P.potentialGeneratorHigh y a U)=
      J (W.commHigh (.inl ()) a U+P.potentialGeneratorHigh y a D)  := by
    rw [map_add]
    exact sub_eq_iff_eq_add.mp hC'
  have h := inclusion_besselOrder_eq_of_half_degree_graph (P.potentialGeneratorHigh y a U)
    (W.commHigh (.inl ()) a U+P.potentialGeneratorHigh y a D) hDeg
  simpa only [forwardFirstWordHigherL,ContinuousLinearMap.comp_apply,_root_.add_apply,U,D] using h

lemma reverseFirstWordHigherL_inclusion (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (W.reverseFirstWordHigherL a u)=
      W.adjointHigh a (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  let U := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
  let D := sphereSobolevShiftedDegreeL (5/2:ℝ) u
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hC := DFunLike.congr_fun (W.commutator_compatible a (.inl ())) U
  have hA := DFunLike.congr_fun (W.adjoint_compatible a) D
  have hDU : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) D=
      P.potentialGeneratorHigh y (.inl ()) U := shiftedDegreeFiveHalf_inclusion u
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply] at hC hA
  rw [hDU] at hA
  have hC' : J (W.adjointHigh a D)-sphereSobolevShiftedDegreeL (1/2:ℝ) (W.adjointHigh a U)=
      J (W.commHigh a (.inl ()) U) := by
    rw [hA]
    exact hC
  have hDeg : sphereSobolevShiftedDegreeL (1/2:ℝ) (W.adjointHigh a U)=
      J (W.adjointHigh a D-W.commHigh a (.inl ()) U)  := by
    rw [map_sub]
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hC').symm)
  have h := inclusion_besselOrder_eq_of_half_degree_graph (W.adjointHigh a U)
    (W.adjointHigh a D-W.commHigh a (.inl ()) U) hDeg
  simpa only [reverseFirstWordHigherL,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,U,D] using h
end PhysicalPotentialQuarticData
end ShrinkingSpheres
