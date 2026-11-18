import Proof.NativeFullRadialAngularFields
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
open Set
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
lemma fullAdjoint_taylor_decomposition (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    t.fullAdjoint p=t.adjointTaylor p+sphereSobolevDegreeL+d.radius y •
      (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
        (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have hh := t.fullAdjointAngularFields_operator p
  change t.adjointTaylor p+(sphereSobolevDegreeL+d.radius y •
    (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))=t.fullAdjoint p at hh
  exact hh.symm.trans (add_assoc _ _ _).symm
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
