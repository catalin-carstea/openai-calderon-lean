import Proof.TaylorGeneratorAdjointDecomposition
import Proof.LowBoundedCorrectionAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- A bounded defect in the actual adjoint identity determines compatible
positive and negative endpoint maps. Both maps use the SAME defect witness. -/
lemma adjoint_defect_bounded_compatible {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (I0 P N : E →L[ℝ] E) (hI : I0.adjoint=I0)
    (hP : P.adjoint=P-N.comp I0) : I0.comp N.adjoint=(-N).comp I0 := by
  have hN : N.comp I0=P-P.adjoint := by rw [hP];abel
  calc
    _ = (N.comp I0).adjoint := by rw [ContinuousLinearMap.adjoint_comp,hI]
    _ = (P-P.adjoint).adjoint := congrArg (fun T : E →L[ℝ] E => T.adjoint) hN
    _ = P.adjoint-P := by rw [map_sub,ContinuousLinearMap.adjoint_adjoint]
    _ = _ := by rw [hP,ContinuousLinearMap.neg_comp];abel

def taylorGeneratorAdjointDefectHalfL
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    TaylorGeneratorIndex → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  | .taylor => KN.adjoint
  | _ => 0

lemma taylorGeneratorAdjointDefect_half_negative_compatible
    (P : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : P.adjoint=P-KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (a : TaylorGeneratorIndex) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (taylorGeneratorAdjointDefectHalfL KN a)=
      (taylorGeneratorAdjointDefectL KN a).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  cases a
  · exact adjoint_defect_bounded_compatible _ P KN sphereSobolevHalfNegativeInclusion_adjoint hP
  · simp only [taylorGeneratorAdjointDefectHalfL,taylorGeneratorAdjointDefectL,
      ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  · simp only [taylorGeneratorAdjointDefectHalfL,taylorGeneratorAdjointDefectL,
      ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]

lemma norm_taylorGeneratorAdjointDefectHalfL_le
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C r : ℝ) (hC : 0 ≤ C) (hKN : ‖KN‖ ≤ C*r^2) (a : TaylorGeneratorIndex) :
    ‖taylorGeneratorAdjointDefectHalfL KN a‖ ≤ C*taylorGeneratorWeight r a := by
  cases a
  · simpa only [taylorGeneratorAdjointDefectHalfL,taylorGeneratorWeight,LinearIsometryEquiv.norm_map] using hKN
  · simpa only [taylorGeneratorAdjointDefectHalfL,taylorGeneratorWeight,norm_zero,mul_one] using hC
  · simpa only [taylorGeneratorAdjointDefectHalfL,taylorGeneratorWeight,norm_zero,mul_one] using hC
end ShrinkingSpheres
