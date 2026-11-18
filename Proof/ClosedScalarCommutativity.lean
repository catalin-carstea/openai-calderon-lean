import Proof.ClosedHigherScalarMultiplier
import Proof.CoframeScalarRotationCalculus
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma closedThreeJetCoarseScalarMultiplier_commute (Q R : ClosedCoefficientJets 3) :
    (closedThreeJetCoarseScalarMultiplierL Q).comp (closedThreeJetCoarseScalarMultiplierL R)=
      (closedThreeJetCoarseScalarMultiplierL R).comp (closedThreeJetCoarseScalarMultiplierL Q) := by
  have hCore (P T : SmoothCoefficientJets 3) :
      (closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 P)).comp
        (closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 T))=
      (closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 T)).comp
        (closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 P)) := by
    rw [closedThreeJetCoarseScalarMultiplierL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth]
    exact coarseSphereScalarMulL_commute _ _
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction_on₂
    (isClosed_eq (by fun_prop) (by fun_prop)) hCore Q R

lemma closedOneBoundaryScalarMultiplier_commute (Q R : ClosedCoefficientJets 3) :
    (closedOneBoundaryScalarMultiplierL Q).comp (closedOneBoundaryScalarMultiplierL R)=
      (closedOneBoundaryScalarMultiplierL R).comp (closedOneBoundaryScalarMultiplierL Q) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,closedThreeJet_scalar_multiplier_compatible]
  exact DFunLike.congr_fun (closedThreeJetCoarseScalarMultiplier_commute Q R)
    (sphereSobolevInclusionL 1 0 (by norm_num) u)

lemma closedThreeJetHalfScalarMultiplier_commute (Q R : ClosedCoefficientJets 3) :
    (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp (closedThreeJetHalfBoundaryScalarMultiplierL R)=
      (closedThreeJetHalfBoundaryScalarMultiplierL R).comp (closedThreeJetHalfBoundaryScalarMultiplierL Q) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,closedThreeJet_half_scalar_multiplier_coarse]
  exact DFunLike.congr_fun (closedThreeJetCoarseScalarMultiplier_commute Q R)
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u)

lemma closedThreeJetHigherScalarMultiplier_commute (Q R : ClosedCoefficientJets 3) :
    (closedThreeJetHigherScalarMultiplierL Q).comp (closedThreeJetHigherScalarMultiplierL R)=
      (closedThreeJetHigherScalarMultiplierL R).comp (closedThreeJetHigherScalarMultiplierL Q) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2:ℝ) 0 (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,closedThreeJet_higher_scalar_multiplier_coarse]
  exact DFunLike.congr_fun (closedThreeJetCoarseScalarMultiplier_commute Q R)
    (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u)

lemma closedThreeJetHigherScalarMultiplier_coordinate_commute (Q : ClosedCoefficientJets 3) (j : I) :
    (closedThreeJetHigherScalarMultiplierL Q).comp (coordinateMultiplierSobolevL (3/2:ℝ) j)=
      (coordinateMultiplierSobolevL (3/2:ℝ) j).comp (closedThreeJetHigherScalarMultiplierL Q) := by
  have hI (v : SphereSobolev (3/2:ℝ)) :
      sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (coordinateMultiplierSobolevL (3/2:ℝ) j v)=
        coordinateMultiplierSobolevL 0 j (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) v) :=
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics (3/2:ℝ) 0 (by norm_num) (axis j) v
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2:ℝ) 0 (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,closedThreeJet_higher_scalar_multiplier_coarse,hI]
  exact DFunLike.congr_fun (closedThreeJetCoarseScalarMultiplier_coordinate_commute Q j)
    (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u)

lemma closedHigherScalar_coframe_commute (Q : ClosedCoefficientJets 3)
    (g : MetricField) (v : X) (p : NormalFrameRelativeParameter) :
    (closedThreeJetHigherScalarMultiplierL Q).comp (relativeCoframeNormalSobolevL (3/2:ℝ) g v p)=
      (relativeCoframeNormalSobolevL (3/2:ℝ) g v p).comp (closedThreeJetHigherScalarMultiplierL Q) :=
  clm_commute_sum_smul _ _ _ (closedThreeJetHigherScalarMultiplier_coordinate_commute Q)
end ShrinkingSpheres
