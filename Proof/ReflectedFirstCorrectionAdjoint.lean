import Proof.FirstFrameCorrectionAdjointHigher
import Proof.Archive.SphereSobolevInclusion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Equality of the NORMALIZED diagonal inclusion operators with gap one,
proved from their Bessel weights. This is an operator calculation, never
a regularity assertion from equality of the underlying carriers. -/
lemma sphereSobolevInclusionL_normalized_gap_one (s t : ℝ) (hst : t ≤ s) (hgap : t-s= -1) :
    sphereSobolevInclusionL s t hst=
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  simp only [sphereSobolevInclusionL_apply]
  rw [hgap,show (-(1/2:ℝ))-(1/2:ℝ)= -1 by norm_num]

def firstFrameCorrectionAdjointThreeHalfL (d : Data) (y : X) (i : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (firstFrameAdjointCorrectionAtL (-(3/2:ℝ)) d y i).adjoint

private lemma reflected_bounded_adjoint_graph {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J C D : E →L[ℝ] E) (hJ : J.adjoint=J) (h : J.comp C=D.comp J) :
    J.comp D.adjoint=C.adjoint.comp J := by
  have ha := congrArg (fun A : E →L[ℝ] E => A.adjoint) h
  simp only [ContinuousLinearMap.adjoint_comp,hJ] at ha
  exact ha.symm

/-- Reflection of the genuine negative-grade correction inclusion gives
the genuine positive higher-adjoint graph. -/
lemma firstFrameCorrectionAdjointThreeHalfL_inclusion (d : Data) (y : X) (i : I) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (firstFrameCorrectionAdjointThreeHalfL d y i)=
      (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hFor : (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
      (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i)=
      (firstFrameAdjointCorrectionAtL (-(3/2:ℝ)) d y i).comp
        (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro u
    exact firstFrameAdjointCorrectionAtL_inclusion (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) d y i u
  have hNeg := sphereSobolevInclusionL_normalized_gap_one (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) (by norm_num)
  have hPos := sphereSobolevInclusionL_normalized_gap_one (3/2:ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let C := firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i
  let D := firstFrameAdjointCorrectionAtL (-(3/2:ℝ)) d y i
  have hForJ : J.comp C=D.comp J :=
    (congrArg (fun I0 => I0.comp C) hNeg.symm).trans
      (hFor.trans (congrArg (fun I0 => D.comp I0) hNeg))
  have hAdj := reflected_bounded_adjoint_graph (E:=SphereSobolev (1/2:ℝ)) J C D
    sphereSobolevHalfNegativeInclusion_adjoint hForJ
  change (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp D.adjoint=
    C.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  exact (congrArg (fun I0 => I0.comp D.adjoint) hPos).trans
    (hAdj.trans (congrArg (fun I0 => C.adjoint.comp I0) hPos.symm))

def firstFrameCorrectionAdjointFiveHalfL (d : Data) (y : X) (i : I) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (firstFrameCorrectionAdjointThreeHalfL d y i).comp
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))

lemma firstFrameCorrectionAdjointFiveHalfL_inclusion (d : Data) (y : X) (i : I) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (firstFrameCorrectionAdjointFiveHalfL d y i)=
      (firstFrameCorrectionAdjointHigherL d y i).comp
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  unfold firstFrameCorrectionAdjointFiveHalfL firstFrameCorrectionAdjointHigherL
  rw [←ContinuousLinearMap.comp_assoc,firstFrameCorrectionAdjointThreeHalfL_inclusion]

end ShrinkingSpheres
