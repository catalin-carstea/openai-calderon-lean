import Proof.FiniteScalarRemainderNorms
import Proof.TaylorGeneratorAdjointDecomposition
import Proof.LowScalarGeneratorCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def taylorScalarAdjointRemainderL
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C : TaylorGeneratorIndex → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ a,((closedThreeJetNegativeScalarMultiplierL (Q a)).comp (taylorGeneratorAdjointDefectL KN a)-
    a.adjointSign • C a)

private lemma finite_right_scalar_adjoint {E κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype κ]
    (G M Mn K C : κ → E →L[ℝ] E) (I0 : E →L[ℝ] E) (sign : κ → ℝ)
    (hG : ∀ a,(G a).adjoint=sign a • G a+(K a).comp I0)
    (hM : ∀ a,(M a).adjoint=Mn a)
    (hC : ∀ a,(G a).comp (M a)-(Mn a).comp (G a)=(C a).comp I0) :
    (∑ a,(G a).comp (M a)).adjoint=(∑ a,sign a • (G a).comp (M a))+
      (∑ a,((Mn a).comp (K a)-sign a • C a)).comp I0 := by
  have hTerm (a : κ) : ((G a).comp (M a)).adjoint=sign a • (G a).comp (M a)+
      ((Mn a).comp (K a)-sign a • C a).comp I0 := by
    have hSwap : (Mn a).comp (G a)=(G a).comp (M a)-(C a).comp I0 := by
      calc
        _ = (G a).comp (M a)-((G a).comp (M a)-(Mn a).comp (G a)) := by abel
        _ = _ := congrArg (fun T => (G a).comp (M a)-T) (hC a)
    rw [ContinuousLinearMap.adjoint_comp,hM a,hG a,ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_smul,hSwap]
    simp only [smul_sub,ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_assoc]
    abel
  rw [map_sum]
  simp only [hTerm,Finset.sum_add_distrib]
  congr 1
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply]

/-- The true dual-half adjoint keeps the SAME unbounded generators with
signed real scalar coefficients. Every reordering error is explicitly bounded
on the negative endpoint. -/
lemma taylor_scalar_adjoint_normal_form
    (P : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : P.adjoint=P-KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (C : TaylorGeneratorIndex → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hC : ∀ a,(taylorGeneratorLow P a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))-
      (closedThreeJetNegativeScalarMultiplierL (Q a)).comp (taylorGeneratorLow P a)=
      (C a).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    (∑ a,(taylorGeneratorLow P a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))).adjoint=
      (∑ a,(taylorGeneratorLow P a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (signedTaylorScalarCoefficients Q a)))+
      (taylorScalarAdjointRemainderL KN C Q).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  have hSigned (a : TaylorGeneratorIndex) :
      (taylorGeneratorLow P a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (signedTaylorScalarCoefficients Q a))=
        a.adjointSign • (taylorGeneratorLow P a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a)) := by
    rw [signedTaylorScalarCoefficients,map_smul,ContinuousLinearMap.comp_smul]
  have hM (a : TaylorGeneratorIndex) : (closedThreeJetHalfBoundaryScalarMultiplierL (Q a)).adjoint=
      closedThreeJetNegativeScalarMultiplierL (Q a) := rfl
  have hMain := finite_right_scalar_adjoint (E:=SphereSobolev (1/2:ℝ))
    (taylorGeneratorLow P) (fun a => closedThreeJetHalfBoundaryScalarMultiplierL (Q a))
    (fun a => closedThreeJetNegativeScalarMultiplierL (Q a)) (taylorGeneratorAdjointDefectL KN) C
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) TaylorGeneratorIndex.adjointSign
    (taylorGeneratorLow_adjoint_decomposition P KN hP) hM hC
  simpa only [← hSigned,taylorScalarAdjointRemainderL] using hMain

lemma norm_taylorScalarAdjointRemainderL_le
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C : TaylorGeneratorIndex → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    ‖taylorScalarAdjointRemainderL KN C Q‖ ≤
      ∑ a,((‖closedThreeJetNegativeScalarMultiplierL‖*‖Q a‖)*‖taylorGeneratorAdjointDefectL KN a‖+‖C a‖) := by
  exact norm_finite_scalar_remainder_le closedThreeJetNegativeScalarMultiplierL
    (taylorGeneratorAdjointDefectL KN) C Q TaylorGeneratorIndex.adjointSign
    (fun a => by cases a <;> norm_num [TaylorGeneratorIndex.adjointSign])
end ShrinkingSpheres
