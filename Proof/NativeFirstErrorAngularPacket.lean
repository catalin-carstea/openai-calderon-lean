import Proof.NativeCenterGradientAngularFields
import Proof.CoordinateCombinationAngularFields
import Proof.NativeFirstAdjointError
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
def NativeRelativeHorizontalTaylorData.firstErrorAngularPacket
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) : CoarseRotationAdjointPacket :=
  let P := s.response.adjointTaylorCoarsePacket V h hK (by norm_num) p hp
  let G := ((boundaryGradientAdjointCoarsePacket (fun j => (C j).closed p)
    (s.response.fullAdjointAngularPacket V h hK (by norm_num) p hp)).smul
      (normalFrameRelativeInverseRadiusFactor p)).smul (d.radius y)⁻¹
  (((P.mulCoordinateCombination (fun j => normalFrameRelativeCoframeValue d.γ a j p)).smul
    (normalFrameRelativeInverseRadiusFactor p)).smul (d.radius y)⁻¹).add
      (P.smul (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a)) |>.add G
end ShrinkingSpheres
