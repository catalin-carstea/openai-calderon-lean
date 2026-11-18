import Proof.ClosedCoefficientLowerJets
import Proof.BoundaryCoefficientMultiplierAlgebra
import Proof.BoundaryMatrixMultiplierLinear
import Mathlib.Analysis.Normed.Operator.Extend
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
local instance closedHalfScalarCompleteHalf : CompleteSpace (SphereSobolev (1/2:ℝ)) := lp.completeSpace

lemma norm_halfBoundaryCoefficientMulL_le_coefficientNorm (Q : SmoothCoefficientJets 2) :
    ‖halfBoundaryCoefficientMulL Q‖ ≤ boundaryHalfMultiplierBudget*‖Q‖ := by
  apply norm_nativeHalfCoefficientMulL_local_C1 Q ‖Q‖ (norm_nonneg _)
  · intro x hx
    have hh := norm_iteratedFDeriv_coefficientValue_le 2 Q 0 (by omega) x
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh
  · intro x hx
    have hh := norm_iteratedFDeriv_coefficientValue_le 2 Q 1 (by omega) x
    simpa only [norm_iteratedFDeriv_one] using hh

def smoothTwoJetHalfBoundaryMultiplierL : SmoothCoefficientJets 2 →L[ℝ]
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  ({ toFun := halfBoundaryCoefficientMulL
     map_add' := halfBoundaryCoefficientMulL_add
     map_smul' := halfBoundaryCoefficientMulL_smul } :
    SmoothCoefficientJets 2 →ₗ[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))).mkContinuous
      boundaryHalfMultiplierBudget norm_halfBoundaryCoefficientMulL_le_coefficientNorm

def closedTwoJetHalfBoundaryScalarMultiplierL : ClosedCoefficientJets 2 →L[ℝ]
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  smoothTwoJetHalfBoundaryMultiplierL.extend (smoothCoefficientClosureInclusionL 2)

lemma closedTwoJetHalfBoundaryScalarMultiplierL_on_smooth (Q : SmoothCoefficientJets 2) :
    closedTwoJetHalfBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 2 Q) = halfBoundaryCoefficientMulL Q :=
  smoothTwoJetHalfBoundaryMultiplierL.extend_eq (denseRange_smoothCoefficientClosureInclusionL 2)
    (show Isometry (smoothCoefficientClosureInclusionL 2) from fun _ _ => rfl).isUniformInducing Q

lemma norm_closedTwoJetHalfBoundaryScalarMultiplierL_le :
    ‖closedTwoJetHalfBoundaryScalarMultiplierL‖ ≤ boundaryHalfMultiplierBudget := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 2),
      ‖closedTwoJetHalfBoundaryScalarMultiplierL Q‖ ≤ boundaryHalfMultiplierBudget*‖Q‖ := by
    rintro _ ⟨Q,rfl⟩
    rw [closedTwoJetHalfBoundaryScalarMultiplierL_on_smooth,norm_smoothCoefficientClosureInclusionL]
    exact norm_halfBoundaryCoefficientMulL_le_coefficientNorm Q
  have hBound (Q : ClosedCoefficientJets 2) :
      ‖closedTwoJetHalfBoundaryScalarMultiplierL Q‖ ≤ boundaryHalfMultiplierBudget*‖Q‖ :=
    (denseRange_smoothCoefficientClosureInclusionL 2).induction hDense
      (isClosed_le closedTwoJetHalfBoundaryScalarMultiplierL.continuous.norm (continuous_const.mul continuous_norm)) Q
  exact ContinuousLinearMap.opNorm_le_bound _ boundaryHalfMultiplierBudget_nonneg hBound

def closedThreeJetHalfBoundaryScalarMultiplierL : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  closedTwoJetHalfBoundaryScalarMultiplierL.comp (closedCoefficientLowerJetsL 2)

lemma closedThreeJetHalfBoundaryScalarMultiplierL_on_smooth (Q : SmoothCoefficientJets 3) :
    closedThreeJetHalfBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q) =
      halfBoundaryCoefficientMulL (smoothMultiplierLowerJets Q) := by
  change closedTwoJetHalfBoundaryScalarMultiplierL (closedCoefficientLowerJetsL 2 (smoothCoefficientClosureInclusionL 3 Q)) = _
  rw [closedCoefficientLowerJetsL_on_smooth,closedTwoJetHalfBoundaryScalarMultiplierL_on_smooth]
  rfl

lemma norm_closedThreeJetHalfBoundaryScalarMultiplierL_le :
    ‖closedThreeJetHalfBoundaryScalarMultiplierL‖ ≤ boundaryHalfMultiplierBudget :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul norm_closedTwoJetHalfBoundaryScalarMultiplierL_le (norm_closedCoefficientLowerJetsL_le 2)
      (norm_nonneg _) boundaryHalfMultiplierBudget_nonneg).trans_eq (mul_one _))
end ShrinkingSpheres
