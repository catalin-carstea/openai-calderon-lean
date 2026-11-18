import Proof.ClosedTwoJetOneBoundaryMultiplier
import Proof.ClosedOneBoundaryScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
local instance closedThreeCoarseMultiplierCompleteZero : CompleteSpace (SphereSobolev 0) := lp.completeSpace

def smoothThreeJetCoarseScalarMultiplier (Q : SmoothCoefficientJets 3) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets Q)))

lemma smoothThreeJetCoarseScalarMultiplier_sub_smul (Q P : SmoothCoefficientJets 3) (c : ℝ) :
    smoothThreeJetCoarseScalarMultiplier (Q-c • P) =
      smoothThreeJetCoarseScalarMultiplier Q-c • smoothThreeJetCoarseScalarMultiplier P := by
  have hValue : smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets (Q-c • P))) =
      smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets Q))-c • smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets P)) := by
    apply ContinuousMap.ext
    intro w
    rfl
  change coarseScalarMultiplierMapL _ = coarseScalarMultiplierMapL _-c • coarseScalarMultiplierMapL _
  simp only [hValue,map_sub,map_smul]

lemma norm_smoothThreeJetCoarseScalarMultiplier_le (Q : SmoothCoefficientJets 3) :
    ‖smoothThreeJetCoarseScalarMultiplier Q‖ ≤ ‖Q‖ := by
  apply (norm_coarseSphereScalarMulL_le _).trans
  apply (ContinuousMap.norm_le _ (norm_nonneg Q)).mpr
  intro w
  have hh := norm_iteratedFDeriv_coefficientValue_le 3 Q 0 (by omega) w.val
  change ‖coefficientValue 3 Q w.val‖ ≤ ‖Q‖
  simpa only [norm_iteratedFDeriv_zero] using hh

def smoothThreeJetCoarseScalarMultiplierL : SmoothCoefficientJets 3 →L[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
  (realLinearMapOfSubSmul smoothThreeJetCoarseScalarMultiplier smoothThreeJetCoarseScalarMultiplier_sub_smul).mkContinuous
    1 (fun Q => (norm_smoothThreeJetCoarseScalarMultiplier_le Q).trans_eq (one_mul _).symm)

def closedThreeJetCoarseScalarMultiplierL : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
  smoothThreeJetCoarseScalarMultiplierL.extend (smoothCoefficientClosureInclusionL 3)

lemma closedThreeJetCoarseScalarMultiplierL_on_smooth (Q : SmoothCoefficientJets 3) :
    closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q) =
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets Q))) :=
  smoothThreeJetCoarseScalarMultiplierL.extend_eq (denseRange_smoothCoefficientClosureInclusionL 3)
    (show Isometry (smoothCoefficientClosureInclusionL 3) from fun _ _ => rfl).isUniformInducing Q

lemma norm_closedThreeJetCoarseScalarMultiplierL_apply_le (Q : ClosedCoefficientJets 3) :
    ‖closedThreeJetCoarseScalarMultiplierL Q‖ ≤ ‖Q‖ := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      ‖closedThreeJetCoarseScalarMultiplierL Q‖ ≤ ‖Q‖ := by
    rintro _ ⟨P,rfl⟩
    rw [closedThreeJetCoarseScalarMultiplierL_on_smooth,norm_smoothCoefficientClosureInclusionL]
    exact norm_smoothThreeJetCoarseScalarMultiplier_le P
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_le closedThreeJetCoarseScalarMultiplierL.continuous.norm continuous_norm) Q

lemma closedThreeJet_scalar_multiplier_compatible (Q : ClosedCoefficientJets 3) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (closedOneBoundaryScalarMultiplierL Q u) =
      closedThreeJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      sphereSobolevInclusionL 1 0 (by norm_num) (closedOneBoundaryScalarMultiplierL Q u) =
        closedThreeJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
    rintro _ ⟨P,rfl⟩
    rw [closedOneBoundaryScalarMultiplierL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth]
    exact oneBoundaryCoefficientMulL_coarse (smoothMultiplierLowerJets P) u
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

end ShrinkingSpheres
