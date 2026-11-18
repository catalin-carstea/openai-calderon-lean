import Proof.Archive.ClosedCoefficientMultiplier
import Proof.Archive.NativeThreeHalfCoefficientMultiplier
import Proof.NativeBoundaryCalculus
import Proof.ClosedHalfScalarCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

def closedThreeJetHigherScalarMultiplierL : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) :=
  ((ContinuousLinearMap.compL ℝ (SphereSobolev (3/2:ℝ)) (BallSobolev 2) (SphereSobolev (3/2:ℝ)))
    (nativeThreeHalfValueTraceL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace)).comp
    (((ContinuousLinearMap.compL ℝ (SphereSobolev (3/2:ℝ)) (BallSobolev 2) (BallSobolev 2)).flip
      fixedHarmonicLiftL).comp (closedCoefficientMultiplierL fixedSobolevCalculus 2))

lemma closedThreeJetHigherScalarMultiplierL_on_smooth (Q : SmoothCoefficientJets 3) :
    closedThreeJetHigherScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q)=
      nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace Q := by
  change (nativeThreeHalfValueTraceL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace).comp
    ((closedCoefficientMultiplierL fixedSobolevCalculus 2 (smoothCoefficientClosureInclusionL 3 Q)).comp
      fixedHarmonicLiftL)=_
  rw [closedCoefficientMultiplierL_eq_on_smooth]
  rfl

lemma closedThreeJet_higher_scalar_multiplier_coarse (Q : ClosedCoefficientJets 3)
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (closedThreeJetHigherScalarMultiplierL Q u)=
      closedThreeJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u) := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (closedThreeJetHigherScalarMultiplierL Q u)=
        closedThreeJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u) := by
    rintro _ ⟨P,rfl⟩
    rw [closedThreeJetHigherScalarMultiplierL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth]
    exact sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace P u
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

lemma closedThreeJet_higher_scalar_multiplier_one (Q : ClosedCoefficientJets 3)
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (closedThreeJetHigherScalarMultiplierL Q u)=
      closedOneBoundaryScalarMultiplierL Q (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u) := by
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  rw [closedThreeJet_scalar_multiplier_compatible]
  simpa only [sphereSobolevInclusionL_trans_apply] using closedThreeJet_higher_scalar_multiplier_coarse Q u

lemma closedThreeJet_higher_scalar_multiplier_half (Q : ClosedCoefficientJets 3)
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (closedThreeJetHigherScalarMultiplierL Q u)=
      closedThreeJetHalfBoundaryScalarMultiplierL Q
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) := by
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_half_scalar_multiplier_coarse]
  simpa only [sphereSobolevInclusionL_trans_apply] using closedThreeJet_higher_scalar_multiplier_coarse Q u
end ShrinkingSpheres
