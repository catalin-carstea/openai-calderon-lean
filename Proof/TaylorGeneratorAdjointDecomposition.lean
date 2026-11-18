import Proof.GradedGeneratorAdjoints
import Proof.HalfTaylorAdjointDefect
import Proof.NativeTaylorGeneratorSystem
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def TaylorGeneratorIndex.adjointSign : TaylorGeneratorIndex → ℝ
  | .taylor => 1
  | .degree => 1
  | .rotation _ _ => -1

def taylorGeneratorAdjointDefectL
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    TaylorGeneratorIndex → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  | .taylor => -KN
  | _ => 0

lemma taylorGeneratorLow_adjoint_decomposition
    (P : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : P.adjoint=P-KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (a : TaylorGeneratorIndex) :
    (taylorGeneratorLow P a).adjoint=a.adjointSign • taylorGeneratorLow P a+
      (taylorGeneratorAdjointDefectL KN a).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  cases a
  · simpa only [taylorGeneratorLow,TaylorGeneratorIndex.adjointSign,taylorGeneratorAdjointDefectL,
      one_smul,ContinuousLinearMap.neg_comp,sub_eq_add_neg] using hP
  · simpa only [taylorGeneratorLow,TaylorGeneratorIndex.adjointSign,taylorGeneratorAdjointDefectL,
      one_smul,ContinuousLinearMap.zero_comp,add_zero] using sphereSobolevShiftedDegreeHalf_adjoint
  · simpa only [taylorGeneratorLow,TaylorGeneratorIndex.adjointSign,taylorGeneratorAdjointDefectL,
      neg_one_smul,ContinuousLinearMap.zero_comp,add_zero] using sphereSobolevRotationHalf_adjoint _ _

def signedTaylorScalarCoefficients (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    TaylorGeneratorIndex → ClosedCoefficientJets 3 := fun a => a.adjointSign • Q a

lemma norm_signedTaylorScalarCoefficients (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) (a : TaylorGeneratorIndex) :
    ‖signedTaylorScalarCoefficients Q a‖=‖Q a‖ := by
  cases a <;> simp only [signedTaylorScalarCoefficients,TaylorGeneratorIndex.adjointSign,one_smul,neg_one_smul,norm_neg]

lemma signedTaylorScalarCoefficients_weighted_sum (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) (r : ℝ) :
    (∑ a,taylorGeneratorWeight r a*‖signedTaylorScalarCoefficients Q a‖)=
      ∑ a,taylorGeneratorWeight r a*‖Q a‖ := by simp only [norm_signedTaylorScalarCoefficients]

lemma norm_taylorGeneratorAdjointDefectL_le
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C r : ℝ) (hC : 0 ≤ C) (hKN : ‖KN‖ ≤ C*r^2) (a : TaylorGeneratorIndex) :
    ‖taylorGeneratorAdjointDefectL KN a‖ ≤ C*taylorGeneratorWeight r a := by
  cases a
  · simpa only [taylorGeneratorAdjointDefectL,taylorGeneratorWeight,norm_neg] using hKN
  · simpa only [taylorGeneratorAdjointDefectL,taylorGeneratorWeight,norm_zero,mul_one] using hC
  · simpa only [taylorGeneratorAdjointDefectL,taylorGeneratorWeight,norm_zero,mul_one] using hC
end ShrinkingSpheres
