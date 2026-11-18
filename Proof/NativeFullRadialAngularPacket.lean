import Proof.NativeTaylorAngularPacket
import Proof.BasicRadialAngularPackets
import Proof.CoarseAngularPacketLinearity
import Proof.NativeRelativeFullAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

def fullAdjointAngularPacket (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) : CoarseRotationAdjointPacket :=
  (t.adjointTaylorCoarsePacket V h hK hZ p hp).add
    (degreeCoarseAdjointPacket.add
      ((firstRadialAdjointCoarsePacket (normalFrameRelativeFirstCovector d.γ d.g₁ p)).smul (d.radius y)))

theorem fullAdjointAngularPacket_operator (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (t.fullAdjointAngularPacket V h hK hZ p hp).operator = t.fullAdjoint p := by
  change t.adjointTaylor p+(sphereSobolevDegreeL+d.radius y •
    (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num))) = _
  change (t.fullAdjoint p-sphereSobolevDegreeL-d.radius y •
    (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))+_ = _
  abel

theorem fullAdjointAngularPacket_adjoint (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (t.fullAdjointAngularPacket V h hK hZ p hp).adjoint = t.response p+sphereSobolevDegreeL := by
  have hB : coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p) =
      radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p) := by
    simp only [coarseFirstRadialVariationL_normalized_covector,inv_one,one_smul]
  change (t.response p-d.radius y •
    (coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))+
      (sphereSobolevDegreeL+d.radius y •
        (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
          (sphereSobolevInclusionL 1 0 (by norm_num))) = _
  rw [hB]
  abel

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
