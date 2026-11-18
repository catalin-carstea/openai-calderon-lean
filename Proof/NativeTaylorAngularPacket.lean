import Proof.CoarseAngularProductPackets
import Proof.NativeRelativeDegreeCompatibleFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

def adjointTaylorCoarsePacket (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) : CoarseRotationAdjointPacket where
  operator := t.adjointTaylor p
  adjoint := t.forwardTaylor p
  angular ij := normalFrameRelativeAngularDerivative d.γ t.adjointTaylor ij.1 ij.2 p
  angularAdjoint ij := normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2 p
  pairing := by
    intro u v
    calc
      _ = ⟪sphereSobolevInclusionL 1 0 (by norm_num) v,t.adjointTaylor p u⟫_ℝ := real_inner_comm _ _
      _ = ⟪t.forwardTaylor p v,sphereSobolevInclusionL 1 0 (by norm_num) u⟫_ℝ := (V.taylorPair p hp v u).symm
      _ = _ := real_inner_comm _ _
  graph ij := native_relative_adjoint_rotation_distribution t V h hK hZ p hp ij.1 ij.2
  angularPairing := by
    intro ij u v
    calc
      _ = ⟪sphereSobolevInclusionL 1 0 (by norm_num) v,
          normalFrameRelativeAngularDerivative d.γ t.adjointTaylor ij.1 ij.2 p u⟫_ℝ := real_inner_comm _ _
      _ = ⟪normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2 p v,
          sphereSobolevInclusionL 1 0 (by norm_num) u⟫_ℝ := (V.angularPair p hp ij.1 ij.2 v u).symm
      _ = _ := real_inner_comm _ _

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
