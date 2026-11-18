import Proof.CoarseAngularFields
import Proof.NativeFullRadialAngularPacket
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

def adjointTaylorAngularFields (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    CoarseAngularFields :=
  ⟨t.adjointTaylor p,t.forwardTaylor p,
    (fun ij => normalFrameRelativeAngularDerivative d.γ t.adjointTaylor ij.1 ij.2 p),
    (fun ij => normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2 p)⟩

def fullAdjointAngularFields (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    CoarseAngularFields :=
  (t.adjointTaylorAngularFields p).add
    ((CoarseAngularFields.ofPacket degreeCoarseAdjointPacket).add
      ((CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket
        (normalFrameRelativeFirstCovector d.γ d.g₁ p))).smul (d.radius y)))

lemma ofPacket_fullAdjointAngularPacket (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    CoarseAngularFields.ofPacket (t.fullAdjointAngularPacket V h hK hZ p hp) = t.fullAdjointAngularFields p := rfl

lemma fullAdjointAngularFields_operator (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    (t.fullAdjointAngularFields p).operator = t.fullAdjoint p := by
  change t.adjointTaylor p+(sphereSobolevDegreeL+d.radius y •
    (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num))) = _
  change (t.fullAdjoint p-sphereSobolevDegreeL-d.radius y •
    (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))+_ = _
  abel

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
