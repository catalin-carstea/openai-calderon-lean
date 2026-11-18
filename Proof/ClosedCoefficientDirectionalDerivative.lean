import Proof.SmoothCoefficientDirectionalJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma smoothCoefficientDirectionalDerivative_sub_smul (r : ℕ) (v : X)
    (Q P : SmoothCoefficientJets (r+1)) (c : ℝ) :
    smoothCoefficientDirectionalDerivative r v (Q-c • P) =
      smoothCoefficientDirectionalDerivative r v Q-c • smoothCoefficientDirectionalDerivative r v P := by
  apply smoothCoefficientJets_ext_of_value r
  simp only [coefficientValue_smoothCoefficientDirectionalDerivative,coefficientValue_sub_local,
    coefficientValue_smul]
  funext x
  have hQ := (contDiff_coefficientValue (r+1) Q).differentiable (by simp) x
  have hP := (contDiff_coefficientValue (r+1) P).differentiable (by simp) x
  rw [fderiv_sub hQ (hP.const_smul c),fderiv_const_smul hP c]
  rfl

def smoothCoefficientDirectionalDerivativeL (r : ℕ) (v : X) :
    SmoothCoefficientJets (r+1) →L[ℝ] SmoothCoefficientJets r :=
  (realLinearMapOfSubSmul (smoothCoefficientDirectionalDerivative r v)
    (smoothCoefficientDirectionalDerivative_sub_smul r v)).mkContinuous
    ‖v‖ (norm_smoothCoefficientDirectionalDerivative_le r v)

def closedCoefficientDirectionalDerivativeL (r : ℕ) (v : X) :
    ClosedCoefficientJets (r+1) →L[ℝ] ClosedCoefficientJets r :=
  ((smoothCoefficientClosureInclusionL r).comp (smoothCoefficientDirectionalDerivativeL r v)).extend
    (smoothCoefficientClosureInclusionL (r+1))

lemma closedCoefficientDirectionalDerivativeL_on_smooth (r : ℕ) (v : X)
    (Q : SmoothCoefficientJets (r+1)) :
    closedCoefficientDirectionalDerivativeL r v (smoothCoefficientClosureInclusionL (r+1) Q) =
      smoothCoefficientClosureInclusionL r (smoothCoefficientDirectionalDerivative r v Q) :=
  ((smoothCoefficientClosureInclusionL r).comp (smoothCoefficientDirectionalDerivativeL r v)).extend_eq
    (denseRange_smoothCoefficientClosureInclusionL (r+1))
    (show Isometry (smoothCoefficientClosureInclusionL (r+1)) from fun _ _ => rfl).isUniformInducing Q

lemma norm_closedCoefficientDirectionalDerivativeL_apply_le (r : ℕ) (v : X)
    (Q : ClosedCoefficientJets (r+1)) :
    ‖closedCoefficientDirectionalDerivativeL r v Q‖ ≤ ‖v‖*‖Q‖ := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL (r+1)),
      ‖closedCoefficientDirectionalDerivativeL r v Q‖ ≤ ‖v‖*‖Q‖ := by
    rintro _ ⟨P,rfl⟩
    rw [closedCoefficientDirectionalDerivativeL_on_smooth,norm_smoothCoefficientClosureInclusionL,
      norm_smoothCoefficientClosureInclusionL]
    exact norm_smoothCoefficientDirectionalDerivative_le r v P
  exact (denseRange_smoothCoefficientClosureInclusionL (r+1)).induction hDense
    (isClosed_le (closedCoefficientDirectionalDerivativeL r v).continuous.norm
      (continuous_const.mul continuous_norm)) Q

end ShrinkingSpheres
