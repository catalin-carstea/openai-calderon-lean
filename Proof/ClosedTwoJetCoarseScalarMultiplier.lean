import Proof.ClosedTwoJetOneBoundaryMultiplier
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
local instance closedTwoCoarseMultiplierCompleteZero : CompleteSpace (SphereSobolev 0) := lp.completeSpace

def smoothTwoJetCoarseScalarMultiplier (Q : SmoothCoefficientJets 2) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData Q))

lemma smoothTwoJetCoarseScalarMultiplier_sub_smul (Q P : SmoothCoefficientJets 2) (c : ℝ) :
    smoothTwoJetCoarseScalarMultiplier (Q-c • P) =
      smoothTwoJetCoarseScalarMultiplier Q-c • smoothTwoJetCoarseScalarMultiplier P := by
  have hValue : smoothSphereValue (coefficientSmoothData (Q-c • P)) =
      smoothSphereValue (coefficientSmoothData Q)-c • smoothSphereValue (coefficientSmoothData P) := by
    apply ContinuousMap.ext
    intro w
    rfl
  change coarseScalarMultiplierMapL _ = coarseScalarMultiplierMapL _-c • coarseScalarMultiplierMapL _
  simp only [hValue,map_sub,map_smul]

lemma norm_smoothTwoJetCoarseScalarMultiplier_le (Q : SmoothCoefficientJets 2) :
    ‖smoothTwoJetCoarseScalarMultiplier Q‖ ≤ ‖Q‖ := by
  apply (norm_coarseSphereScalarMulL_le _).trans
  apply (ContinuousMap.norm_le _ (norm_nonneg Q)).mpr
  intro w
  have hh := norm_iteratedFDeriv_coefficientValue_le 2 Q 0 (by omega) w.val
  change ‖coefficientValue 2 Q w.val‖ ≤ ‖Q‖
  simpa only [norm_iteratedFDeriv_zero] using hh

def smoothTwoJetCoarseScalarMultiplierL : SmoothCoefficientJets 2 →L[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
  (realLinearMapOfSubSmul smoothTwoJetCoarseScalarMultiplier smoothTwoJetCoarseScalarMultiplier_sub_smul).mkContinuous
    1 (fun Q => (norm_smoothTwoJetCoarseScalarMultiplier_le Q).trans_eq (one_mul _).symm)

def closedTwoJetCoarseScalarMultiplierL : ClosedCoefficientJets 2 →L[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
  smoothTwoJetCoarseScalarMultiplierL.extend (smoothCoefficientClosureInclusionL 2)

lemma closedTwoJetCoarseScalarMultiplierL_on_smooth (Q : SmoothCoefficientJets 2) :
    closedTwoJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 2 Q) =
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData Q)) :=
  smoothTwoJetCoarseScalarMultiplierL.extend_eq (denseRange_smoothCoefficientClosureInclusionL 2)
    (show Isometry (smoothCoefficientClosureInclusionL 2) from fun _ _ => rfl).isUniformInducing Q

lemma norm_closedTwoJetCoarseScalarMultiplierL_apply_le (Q : ClosedCoefficientJets 2) :
    ‖closedTwoJetCoarseScalarMultiplierL Q‖ ≤ ‖Q‖ := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 2),
      ‖closedTwoJetCoarseScalarMultiplierL Q‖ ≤ ‖Q‖ := by
    rintro _ ⟨P,rfl⟩
    rw [closedTwoJetCoarseScalarMultiplierL_on_smooth,norm_smoothCoefficientClosureInclusionL]
    exact norm_smoothTwoJetCoarseScalarMultiplier_le P
  exact (denseRange_smoothCoefficientClosureInclusionL 2).induction hDense
    (isClosed_le closedTwoJetCoarseScalarMultiplierL.continuous.norm continuous_norm) Q

lemma closedTwoJet_scalar_multiplier_compatible (Q : ClosedCoefficientJets 2) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (closedTwoJetOneBoundaryScalarMultiplierL Q u) =
      closedTwoJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 2),
      sphereSobolevInclusionL 1 0 (by norm_num) (closedTwoJetOneBoundaryScalarMultiplierL Q u) =
        closedTwoJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
    rintro _ ⟨P,rfl⟩
    rw [closedTwoJetOneBoundaryScalarMultiplierL_on_smooth,closedTwoJetCoarseScalarMultiplierL_on_smooth]
    exact oneBoundaryCoefficientMulL_coarse P u
  exact (denseRange_smoothCoefficientClosureInclusionL 2).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

end ShrinkingSpheres
