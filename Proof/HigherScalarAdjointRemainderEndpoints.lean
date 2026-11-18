import Proof.TaylorScalarAdjointRemainderEndpoints
import Proof.ClosedHigherScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def taylorGeneratorAdjointDefectHigherL
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) :
    TaylorGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)
  | .taylor => -KH
  | _ => 0

lemma taylorGeneratorAdjointDefect_higher_half_compatible
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hK : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) (a : TaylorGeneratorIndex) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (taylorGeneratorAdjointDefectHigherL KH a)=
      (taylorGeneratorAdjointDefectHalfL KN a).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  cases a with
  | taylor =>
    simpa only [taylorGeneratorAdjointDefectHigherL,taylorGeneratorAdjointDefectHalfL,
      ContinuousLinearMap.comp_neg,ContinuousLinearMap.neg_comp,neg_neg] using congrArg Neg.neg hK
  | degree => simp only [taylorGeneratorAdjointDefectHigherL,taylorGeneratorAdjointDefectHalfL,
      ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  | rotation i j => simp only [taylorGeneratorAdjointDefectHigherL,taylorGeneratorAdjointDefectHalfL,
      ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]

lemma norm_taylorGeneratorAdjointDefectHigherL_le
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (C r : ℝ) (hC : 0 ≤ C) (hKH : ‖KH‖ ≤ C*r^2) (a : TaylorGeneratorIndex) :
    ‖taylorGeneratorAdjointDefectHigherL KH a‖ ≤ C*taylorGeneratorWeight r a := by
  cases a
  · simpa only [taylorGeneratorAdjointDefectHigherL,taylorGeneratorWeight,norm_neg] using hKH
  · simpa only [taylorGeneratorAdjointDefectHigherL,taylorGeneratorWeight,norm_zero,mul_one] using hC
  · simpa only [taylorGeneratorAdjointDefectHigherL,taylorGeneratorWeight,norm_zero,mul_one] using hC

def taylorScalarAdjointRemainderHigherL
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (C : TaylorGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  ∑ a,((closedThreeJetHigherScalarMultiplierL (Q a)).comp (taylorGeneratorAdjointDefectHigherL KH a)-
    a.adjointSign • C a)

lemma taylorScalarAdjointRemainder_higher_half_compatible
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : TaylorGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (C : TaylorGeneratorIndex → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (hK : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hC : ∀ a,(sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (Ch a)=
      (C a).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (taylorScalarAdjointRemainderHigherL KH Ch Q)=
      (taylorScalarAdjointRemainderHalfL KN C Q).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  finite_scalar_remainder_endpoint_compatible _ _ _ _ _ _ _ TaylorGeneratorIndex.adjointSign
    (fun a => ContinuousLinearMap.ext (closedThreeJet_higher_scalar_multiplier_half (Q a)))
    (taylorGeneratorAdjointDefect_higher_half_compatible KH KN hK) hC
end ShrinkingSpheres
