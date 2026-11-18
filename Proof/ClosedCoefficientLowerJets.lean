import Proof.SmoothCoefficientDirectionalJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

def smoothCoefficientLowerJets (r : ℕ) (Q : SmoothCoefficientJets (r+1)) : SmoothCoefficientJets r :=
  compactCoefficient r (coefficientValue (r+1) Q) (contDiff_coefficientValue (r+1) Q)
    (hasCompactSupport_coefficientValue (r+1) Q)
lemma coefficientValue_smoothCoefficientLowerJets (r : ℕ) (Q : SmoothCoefficientJets (r+1)) :
    coefficientValue r (smoothCoefficientLowerJets r Q) = coefficientValue (r+1) Q :=
  coefficientValue_compactCoefficient _ _ _ _
lemma smoothCoefficientLowerJets_sub_smul (r : ℕ) (Q P : SmoothCoefficientJets (r+1)) (c : ℝ) :
    smoothCoefficientLowerJets r (Q-c • P) = smoothCoefficientLowerJets r Q-c • smoothCoefficientLowerJets r P := by
  apply smoothCoefficientJets_ext_of_value r
  simp only [coefficientValue_smoothCoefficientLowerJets,coefficientValue_sub_local,coefficientValue_smul]
lemma norm_smoothCoefficientLowerJets_le (r : ℕ) (Q : SmoothCoefficientJets (r+1)) :
    ‖smoothCoefficientLowerJets r Q‖ ≤ ‖Q‖ := by
  apply norm_compactCoefficient_le_of_jets r _ _ _ ‖Q‖ (norm_nonneg _)
  intro n hn x
  exact norm_iteratedFDeriv_coefficientValue_le (r+1) Q n (by omega) x

def smoothCoefficientLowerJetsL (r : ℕ) : SmoothCoefficientJets (r+1) →L[ℝ] SmoothCoefficientJets r :=
  (realLinearMapOfSubSmul (smoothCoefficientLowerJets r) (smoothCoefficientLowerJets_sub_smul r)).mkContinuous 1
    (fun Q => (norm_smoothCoefficientLowerJets_le r Q).trans_eq (one_mul _).symm)

def closedCoefficientLowerJetsL (r : ℕ) : ClosedCoefficientJets (r+1) →L[ℝ] ClosedCoefficientJets r :=
  ((smoothCoefficientClosureInclusionL r).comp (smoothCoefficientLowerJetsL r)).extend
    (smoothCoefficientClosureInclusionL (r+1))
lemma closedCoefficientLowerJetsL_on_smooth (r : ℕ) (Q : SmoothCoefficientJets (r+1)) :
    closedCoefficientLowerJetsL r (smoothCoefficientClosureInclusionL (r+1) Q) =
      smoothCoefficientClosureInclusionL r (smoothCoefficientLowerJets r Q) :=
  ((smoothCoefficientClosureInclusionL r).comp (smoothCoefficientLowerJetsL r)).extend_eq
    (denseRange_smoothCoefficientClosureInclusionL (r+1))
    (show Isometry (smoothCoefficientClosureInclusionL (r+1)) from fun _ _ => rfl).isUniformInducing Q
lemma norm_closedCoefficientLowerJetsL_apply_le (r : ℕ) (Q : ClosedCoefficientJets (r+1)) :
    ‖closedCoefficientLowerJetsL r Q‖ ≤ ‖Q‖ := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL (r+1)),‖closedCoefficientLowerJetsL r Q‖ ≤ ‖Q‖ := by
    rintro _ ⟨P,rfl⟩
    rw [closedCoefficientLowerJetsL_on_smooth,norm_smoothCoefficientClosureInclusionL,norm_smoothCoefficientClosureInclusionL]
    exact norm_smoothCoefficientLowerJets_le r P
  exact (denseRange_smoothCoefficientClosureInclusionL (r+1)).induction hDense
    (isClosed_le (closedCoefficientLowerJetsL r).continuous.norm continuous_norm) Q
lemma norm_closedCoefficientLowerJetsL_le (r : ℕ) : ‖closedCoefficientLowerJetsL r‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Q => (norm_closedCoefficientLowerJetsL_apply_le r Q).trans_eq (one_mul _).symm)
end ShrinkingSpheres
