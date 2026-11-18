import Proof.BoundaryMatrixMultiplierLinear
import Proof.OrderOneCoefficientAlgebra
import Proof.BoundaryScalarGeneratorDerivative
import Proof.Archive.NativeH2SmoothMultiplierDerivative
import Proof.DenseIsometryOperatorExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
local instance closedTwoScalarMultiplierCompleteOne : CompleteSpace (SphereSobolev 1) := lp.completeSpace

def smoothTwoJetOneBoundaryMultiplier (Q : SmoothCoefficientJets 2) : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  oneBoundaryCoefficientMulL Q

lemma smoothTwoJetOneBoundaryMultiplier_sub_smul (F G : SmoothCoefficientJets 2) (c : ℝ) :
    smoothTwoJetOneBoundaryMultiplier (F-c • G) =
      smoothTwoJetOneBoundaryMultiplier F-c • smoothTwoJetOneBoundaryMultiplier G := by
  exact (oneBoundaryCoefficientMulL_sub F (c • G)).trans
    (congrArg (fun T => oneBoundaryCoefficientMulL F-T) (oneBoundaryCoefficientMulL_smul c G))

lemma norm_smoothTwoJetOneBoundaryMultiplier_le (Q : SmoothCoefficientJets 2) :
    ‖smoothTwoJetOneBoundaryMultiplier Q‖ ≤ 73*‖Q‖ := by
  apply norm_oneBoundaryCoefficientMulL_local_C1 _ ‖Q‖ (norm_nonneg _)
  intro z hz
  constructor
  · have hh := norm_iteratedFDeriv_coefficientValue_le 2 Q 0 (by omega) z
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh
  · have hh := norm_iteratedFDeriv_coefficientValue_le 2 Q 1 (by omega) z
    simpa only [norm_iteratedFDeriv_one] using hh

def smoothTwoJetOneBoundaryMultiplierL : SmoothCoefficientJets 2 →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 1) :=
  (realLinearMapOfSubSmul smoothTwoJetOneBoundaryMultiplier smoothTwoJetOneBoundaryMultiplier_sub_smul).mkContinuous
    73 norm_smoothTwoJetOneBoundaryMultiplier_le

def closedTwoJetOneBoundaryScalarMultiplierL : ClosedCoefficientJets 2 →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 1) :=
  smoothTwoJetOneBoundaryMultiplierL.extend (smoothCoefficientClosureInclusionL 2)

theorem closedTwoJetOneBoundaryScalarMultiplierL_on_smooth (Q : SmoothCoefficientJets 2) :
    closedTwoJetOneBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 2 Q) =
      oneBoundaryCoefficientMulL Q :=
  smoothTwoJetOneBoundaryMultiplierL.extend_eq (denseRange_smoothCoefficientClosureInclusionL 2)
    (show Isometry (smoothCoefficientClosureInclusionL 2) from fun _ _ => rfl).isUniformInducing Q

theorem norm_closedTwoJetOneBoundaryScalarMultiplierL_le : ‖closedTwoJetOneBoundaryScalarMultiplierL‖ ≤ 73 := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 2),
      ‖closedTwoJetOneBoundaryScalarMultiplierL Q‖ ≤ 73*‖Q‖ := by
    rintro _ ⟨Q,rfl⟩
    rw [closedTwoJetOneBoundaryScalarMultiplierL_on_smooth,norm_smoothCoefficientClosureInclusionL]
    exact norm_smoothTwoJetOneBoundaryMultiplier_le Q
  have hBound (Q : ClosedCoefficientJets 2) : ‖closedTwoJetOneBoundaryScalarMultiplierL Q‖ ≤ 73*‖Q‖ :=
    (denseRange_smoothCoefficientClosureInclusionL 2).induction hDense
      (isClosed_le closedTwoJetOneBoundaryScalarMultiplierL.continuous.norm (continuous_const.mul continuous_norm)) Q
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hBound

end ShrinkingSpheres
