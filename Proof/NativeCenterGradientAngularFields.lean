import Proof.NativeFullRadialAngularFields
import Proof.RelativeCenterGradientAdjointFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

def NativeRelativeHorizontalTaylorData.centerGradientAngularFields
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) : CoarseAngularFields :=
  (((s.response.fullAdjointAngularFields p).gradient (fun j => (C j).closed p)).smul
    (normalFrameRelativeInverseRadiusFactor p)).smul (d.radius y)⁻¹

lemma NativeRelativeHorizontalTaylorData.centerGradientAngularFields_operator
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) :
    (s.centerGradientAngularFields C p).operator = s.centerGradientAdjointFamily C p := by
  change (d.radius y)⁻¹ • (normalFrameRelativeInverseRadiusFactor p •
    (CoarseAngularFields.gradient _ (s.response.fullAdjointAngularFields p)).operator) = _
  rw [CoarseAngularFields.gradient_operator,s.response.fullAdjointAngularFields_operator]
  rfl

lemma NativeRelativeHorizontalTaylorData.centerGradientAngularFields_compatible
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (s.centerGradientAngularFields C p).degreeData ∈ CoarseDegreeCompatibility.compatibleData := by
  let P := ((boundaryGradientAdjointCoarsePacket (fun j => (C j).closed p)
    (s.response.fullAdjointAngularPacket V h hK (by norm_num) p hp)).smul
      (normalFrameRelativeInverseRadiusFactor p)).smul (d.radius y)⁻¹
  have hFields : CoarseAngularFields.ofPacket P = s.centerGradientAngularFields C p := rfl
  rw [← hFields]
  exact P.data_mem

end ShrinkingSpheres
