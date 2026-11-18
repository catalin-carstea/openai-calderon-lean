import Proof.ClosedCoefficientDirectionalDerivative
import Proof.ClosedCoefficientLowerJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma closedCoefficientDirectionalDerivative_lowerJets (r : ℕ) (v : X)
    (Q : ClosedCoefficientJets (r+2)) :
    closedCoefficientLowerJetsL r (closedCoefficientDirectionalDerivativeL (r+1) v Q)=
      closedCoefficientDirectionalDerivativeL r v (closedCoefficientLowerJetsL (r+1) Q) := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL (r+2)),
      closedCoefficientLowerJetsL r (closedCoefficientDirectionalDerivativeL (r+1) v Q)=
        closedCoefficientDirectionalDerivativeL r v (closedCoefficientLowerJetsL (r+1) Q) := by
    rintro _ ⟨P,rfl⟩
    rw [closedCoefficientDirectionalDerivativeL_on_smooth,closedCoefficientLowerJetsL_on_smooth,
      closedCoefficientLowerJetsL_on_smooth,closedCoefficientDirectionalDerivativeL_on_smooth]
    apply congrArg (smoothCoefficientClosureInclusionL r)
    apply smoothCoefficientJets_ext_of_value r
    simp only [coefficientValue_smoothCoefficientLowerJets,coefficientValue_smoothCoefficientDirectionalDerivative]
  exact (denseRange_smoothCoefficientClosureInclusionL (r+2)).induction hDense
    (isClosed_eq ((closedCoefficientLowerJetsL r).continuous.comp
      (closedCoefficientDirectionalDerivativeL (r+1) v).continuous)
      ((closedCoefficientDirectionalDerivativeL r v).continuous.comp (closedCoefficientLowerJetsL (r+1)).continuous)) Q
end ShrinkingSpheres
