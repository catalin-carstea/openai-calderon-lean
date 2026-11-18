import Proof.ClosedHigherScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- A SAME positive-half scalar commutator determines its genuine higher
endpoint square by the physical coarse graph and canonical multiplier maps. -/
lemma balanced_higher_scalar_commutator
    (E : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (Q : ClosedCoefficientJets 3)
    (hHi : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      E.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hC : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (C.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=
        E.comp (closedOneBoundaryScalarMultiplierL Q)-(closedThreeJetCoarseScalarMultiplierL Q).comp E) :
    Hi.comp (closedThreeJetHigherScalarMultiplierL Q)-(closedThreeJetHalfBoundaryScalarMultiplierL Q).comp Hi=
      C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  have hH (v : SphereSobolev (3/2:ℝ)) :
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (Hi v)=
        E (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) v) := DFunLike.congr_fun hHi v
  have hComm (v : SphereSobolev 1) :
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (C (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v))=
        E (closedOneBoundaryScalarMultiplierL Q v)-closedThreeJetCoarseScalarMultiplierL Q (E v) :=
    DFunLike.congr_fun hC v
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (Hi (closedThreeJetHigherScalarMultiplierL Q u)-closedThreeJetHalfBoundaryScalarMultiplierL Q (Hi u))=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))
  rw [map_sub,hH,closedThreeJet_half_scalar_multiplier_coarse,
    closedThreeJet_higher_scalar_multiplier_one,hH,← hComm]
  rw [sphereSobolevInclusionL_trans_apply]
end ShrinkingSpheres
