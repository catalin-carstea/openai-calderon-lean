import Proof.ClosedHalfScalarMultiplier
import Proof.ClosedTwoJetCoarseScalarMultiplier
import Proof.ClosedThreeJetCoarseScalarMultiplier
import Proof.RightMultiplierRotationGraph
import Proof.ActualRadialTaylorEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier OAI.AnisotropicCalderon.NativeHalfSmoothMultiplier

lemma halfBoundaryCoefficientMulL_coarse (Q : SmoothCoefficientJets 2) (u : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (halfBoundaryCoefficientMulL Q u) =
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData Q))
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData Q)
  dsimp only [halfBoundaryCoefficientMulL]
  rw [nativeHalfCoefficientMulL_eq_smoothMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace Q hM hm hg]
  exact sphereSobolevInclusionL_nativeHalfSmoothMulL sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace (coefficientSmoothData Q) hM hm hg u

lemma closedTwoJet_half_scalar_multiplier_coarse (Q : ClosedCoefficientJets 2) (u : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (closedTwoJetHalfBoundaryScalarMultiplierL Q u) =
      closedTwoJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u) := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 2),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (closedTwoJetHalfBoundaryScalarMultiplierL Q u) =
        closedTwoJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u) := by
    rintro _ ⟨P,rfl⟩
    rw [closedTwoJetHalfBoundaryScalarMultiplierL_on_smooth,closedTwoJetCoarseScalarMultiplierL_on_smooth]
    exact halfBoundaryCoefficientMulL_coarse P u
  exact (denseRange_smoothCoefficientClosureInclusionL 2).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

lemma closedTwoJetCoarseScalarMultiplier_lowerJets (Q : ClosedCoefficientJets 3) :
    closedTwoJetCoarseScalarMultiplierL (closedCoefficientLowerJetsL 2 Q) = closedThreeJetCoarseScalarMultiplierL Q := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      closedTwoJetCoarseScalarMultiplierL (closedCoefficientLowerJetsL 2 Q) = closedThreeJetCoarseScalarMultiplierL Q := by
    rintro _ ⟨P,rfl⟩
    rw [closedCoefficientLowerJetsL_on_smooth,closedTwoJetCoarseScalarMultiplierL_on_smooth,
      closedThreeJetCoarseScalarMultiplierL_on_smooth]
    rfl
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

lemma closedThreeJet_half_scalar_multiplier_coarse (Q : ClosedCoefficientJets 3) (u : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (closedThreeJetHalfBoundaryScalarMultiplierL Q u) =
      closedThreeJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u) := by
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (closedTwoJetHalfBoundaryScalarMultiplierL (closedCoefficientLowerJetsL 2 Q) u) = _
  rw [closedTwoJet_half_scalar_multiplier_coarse,closedTwoJetCoarseScalarMultiplier_lowerJets]

lemma closedThreeJet_scalar_multiplier_one_half (Q : ClosedCoefficientJets 3) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (closedOneBoundaryScalarMultiplierL Q u) =
      closedThreeJetHalfBoundaryScalarMultiplierL Q (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) := by
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_half_scalar_multiplier_coarse]
  simp only [sphereSobolevInclusionL_trans_apply]
  exact closedThreeJet_scalar_multiplier_compatible Q u
end ShrinkingSpheres
