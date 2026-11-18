import Proof.ActualRadialTaylorEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- An order-zero realization of a commutator through two explicit inclusions. -/
def CommutatorLift {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (I0 : E →L[ℝ] G) (I1 : F →L[ℝ] G) (M1 : F →L[ℝ] F) (M0 : E →L[ℝ] E)
    (D : F →L[ℝ] E) (K : G →L[ℝ] G) : Prop := I0.comp (D.comp M1-M0.comp D)=K.comp I1

namespace CommutatorLift
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {I0 : E →L[ℝ] G} {I1 : F →L[ℝ] G} {M1 : F →L[ℝ] F} {M0 : E →L[ℝ] E}
    {D A : F →L[ℝ] E} {K L : G →L[ℝ] G}

lemma add (hD : CommutatorLift I0 I1 M1 M0 D K) (hA : CommutatorLift I0 I1 M1 M0 A L) :
    CommutatorLift I0 I1 M1 M0 (D+A) (K+L) := by
  change I0.comp ((D+A).comp M1-M0.comp (D+A))=(K+L).comp I1
  calc
    _ = I0.comp (D.comp M1-M0.comp D)+I0.comp (A.comp M1-M0.comp A) := by
      rw [← ContinuousLinearMap.comp_add]
      congr 1
      simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add]
      abel
    _ = _ := by rw [hD,hA,ContinuousLinearMap.add_comp]

lemma smul (hD : CommutatorLift I0 I1 M1 M0 D K) (c : ℝ) :
    CommutatorLift I0 I1 M1 M0 (c • D) (c • K) := by
  change I0.comp ((c • D).comp M1-M0.comp (c • D))=(c • K).comp I1
  rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,← smul_sub,
    ContinuousLinearMap.comp_smul,hD,ContinuousLinearMap.smul_comp]

lemma sum {κ : Type*} [Fintype κ] (D : κ → F →L[ℝ] E) (K : κ → G →L[ℝ] G)
    (h : ∀ k,CommutatorLift I0 I1 M1 M0 (D k) (K k)) :
    CommutatorLift I0 I1 M1 M0 (∑ k,D k) (∑ k,K k) := by
  apply ContinuousLinearMap.ext
  intro u
  change I0 ((∑ k,D k) (M1 u)-M0 ((∑ k,D k) u))=(∑ k,K k) (I1 u)
  simp only [_root_.sum_apply,map_sum,map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [ContinuousLinearMap.comp_apply,_root_.sub_apply,map_sub] using
    congrArg (fun T : F →L[ℝ] G => T u) (h k)
end CommutatorLift

lemma negative_commutator_comp_right
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (M1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (M0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (K : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (CN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hD : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (D.comp M1-M0.comp D) = K.comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)))
    (hComm : C1.comp M1=M1.comp C1)
    (hC : ∀ u,sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num) (C1 u) =
      CN (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num) u)) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      ((D.comp C1).comp M1-M0.comp (D.comp C1)) =
      (K.comp CN).comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hCommU := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 1 => T u) hComm
  have hDU := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T (C1 u)) hD
  change C1 (M1 u)=M1 (C1 u) at hCommU
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (D (M1 (C1 u))-M0 (D (C1 u))) = K (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num) (C1 u)) at hDU
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (D (C1 (M1 u))-M0 (D (C1 u))) = K (CN (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num) u))
  rw [hCommU,hDU,hC]
end ShrinkingSpheres
