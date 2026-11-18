import Proof.RadialScalarBoundedEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def radialScalarBoundedCoarseL (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ((radialCorrectionCovectorL ell).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))).comp
    (closedOneBoundaryScalarMultiplierL Q)

lemma radialScalarBounded_coarse_endpoints (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (radialScalarBoundedCoarseL ell Q)=
      ((radialScalarBoundedNegativeL ell Q).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((radialScalarBoundedHalfL ell Q).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))=
      (radialScalarBoundedCoarseL ell Q).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro u
    have hR := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
      (radialScalarBoundedHalf_coarse_compatible ell Q u)
    have hP := DFunLike.congr_fun (radialScalarBounded_half_negative_compatible ell Q)
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)
    have hR' : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (radialScalarBoundedHalfL ell Q (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (radialScalarBoundedCoarseL ell Q u) := by
      simpa only [sphereSobolevInclusionL_trans_apply,radialScalarBoundedCoarseL,ContinuousLinearMap.comp_apply] using hR
    exact hR'.symm.trans hP
  · apply ContinuousLinearMap.ext
    intro u
    have hR := radialScalarBoundedHalf_coarse_compatible ell Q
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
    simpa only [radialScalarBoundedCoarseL,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hR
end ShrinkingSpheres
