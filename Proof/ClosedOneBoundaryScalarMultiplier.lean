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
local instance closedScalarMultiplierCompleteOne : CompleteSpace (SphereSobolev 1) := lp.completeSpace

def smoothThreeJetOneBoundaryMultiplier (Q : SmoothCoefficientJets 3) : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q)

lemma smoothThreeJetOneBoundaryMultiplier_sub_smul (F G : SmoothCoefficientJets 3) (c : ℝ) :
    smoothThreeJetOneBoundaryMultiplier (F-c • G) =
      smoothThreeJetOneBoundaryMultiplier F-c • smoothThreeJetOneBoundaryMultiplier G := by
  have hEq := oneBoundaryCoefficientMulL_congr_sphere (smoothMultiplierLowerJets (F-c • G))
    (smoothMultiplierLowerJets F-c • smoothMultiplierLowerJets G) (by
      intro w
      simp only [coefficientValue_smoothMultiplierLowerJets,coefficientValue_sub_local,coefficientValue_smul])
  exact hEq.trans ((oneBoundaryCoefficientMulL_sub _ _).trans
    (congrArg (fun T => oneBoundaryCoefficientMulL (smoothMultiplierLowerJets F)-T)
      (oneBoundaryCoefficientMulL_smul c _)))

lemma norm_smoothThreeJetOneBoundaryMultiplier_le (Q : SmoothCoefficientJets 3) :
    ‖smoothThreeJetOneBoundaryMultiplier Q‖ ≤ 73*‖Q‖ := by
  apply norm_oneBoundaryCoefficientMulL_local_C1 _ ‖Q‖ (norm_nonneg _)
  rw [coefficientValue_smoothMultiplierLowerJets]
  intro z hz
  constructor
  · have hh := norm_iteratedFDeriv_coefficientValue_le 3 Q 0 (by omega) z
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh
  · have hh := norm_iteratedFDeriv_coefficientValue_le 3 Q 1 (by omega) z
    simpa only [norm_iteratedFDeriv_one] using hh

def smoothThreeJetOneBoundaryMultiplierL : SmoothCoefficientJets 3 →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 1) :=
  (realLinearMapOfSubSmul smoothThreeJetOneBoundaryMultiplier smoothThreeJetOneBoundaryMultiplier_sub_smul).mkContinuous
    73 norm_smoothThreeJetOneBoundaryMultiplier_le

def closedOneBoundaryScalarMultiplierL : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 1) :=
  smoothThreeJetOneBoundaryMultiplierL.extend (smoothCoefficientClosureInclusionL 3)

theorem closedOneBoundaryScalarMultiplierL_on_smooth (Q : SmoothCoefficientJets 3) :
    closedOneBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q) =
      oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q) :=
  smoothThreeJetOneBoundaryMultiplierL.extend_eq (denseRange_smoothCoefficientClosureInclusionL 3)
    (show Isometry (smoothCoefficientClosureInclusionL 3) from fun _ _ => rfl).isUniformInducing Q

theorem norm_closedOneBoundaryScalarMultiplierL_le : ‖closedOneBoundaryScalarMultiplierL‖ ≤ 73 := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      ‖closedOneBoundaryScalarMultiplierL Q‖ ≤ 73*‖Q‖ := by
    rintro _ ⟨Q,rfl⟩
    rw [closedOneBoundaryScalarMultiplierL_on_smooth,norm_smoothCoefficientClosureInclusionL]
    exact norm_smoothThreeJetOneBoundaryMultiplier_le Q
  have hBound (Q : ClosedCoefficientJets 3) : ‖closedOneBoundaryScalarMultiplierL Q‖ ≤ 73*‖Q‖ :=
    (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
      (isClosed_le closedOneBoundaryScalarMultiplierL.continuous.norm (continuous_const.mul continuous_norm)) Q
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hBound

end ShrinkingSpheres
