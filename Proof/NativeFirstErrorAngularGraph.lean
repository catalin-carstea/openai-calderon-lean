import Proof.NativeFirstErrorAngularFields
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2200
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
lemma NativeRelativeHorizontalTaylorData.firstErrorAngularFields_rotation_graph
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (i j : I) (u : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (s.firstAdjointErrorFamily C p (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        ((s.firstErrorAngularFields C p).angular (i,j) (sphereSobolevInclusionL 2 1 (by norm_num) u)+
          s.firstAdjointErrorFamily C p (sphereSobolevRotationL 2 i j u)) := by
  let F := s.firstErrorAngularPacket C V h hK p hp
  have hFields : CoarseAngularFields.ofPacket F=s.firstErrorAngularFields C p := rfl
  have hOp : F.operator=s.firstAdjointErrorFamily C p :=
    (congrArg CoarseAngularFields.operator hFields).trans (s.firstErrorAngularFields_operator C p)
  have hAng : F.angular (i,j)=(s.firstErrorAngularFields C p).angular (i,j) :=
    congrArg (fun P : CoarseAngularFields => P.angular (i,j)) hFields
  have hGraph := F.graph (i,j) u
  rw [hOp,hAng] at hGraph
  exact hGraph
end ShrinkingSpheres
