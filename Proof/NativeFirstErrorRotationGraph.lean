import Proof.NativeFirstErrorAngularGraph
import Proof.NativeFirstErrorAngularNaturality
import Proof.NativeFirstErrorAngularPacket
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
lemma NativeRelativeHorizontalTaylorData.firstError_normalized_rotation_graph
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V) (hpC : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0)
    (i j : I) (u : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (s.firstAdjointErrorFamily C p (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (normalFrameRelativeAngularDerivative d.γ (s.firstAdjointErrorFamily C) i j p
          (sphereSobolevInclusionL 2 1 (by norm_num) u)+
            s.firstAdjointErrorFamily C p (sphereSobolevRotationL 2 i j u)) := by
  have hGraph := s.firstErrorAngularFields_rotation_graph C V h hK p hp.1 i j u
  rw [s.firstErrorAngularFields_angular_eq C V hY hΩ h hK hProfile p hp hpC he i j] at hGraph
  exact hGraph

end ShrinkingSpheres
