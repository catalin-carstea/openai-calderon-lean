import Proof.NativeFullRadialAngularFields
import Proof.FirstRadialAngularFieldJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

lemma adjointTaylorAngularFields_smoothAt (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    CoarseAngularFields.SmoothAt t.adjointTaylorAngularFields p := by
  have hpN := V.normalizationStable p hp
  have hNorm : ContDiffAt ℝ ∞ (normalFrameRelativeNormalization d.γ) p :=
    (h.contDiffOn_normalFrameRelativeNormalization hΩ hK).contDiffAt
      ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds (q.positive (t.sub (V.sub hp))))
  have hF := t.contDiffOn_forwardTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hp))
  have hA := t.contDiffOn_adjointTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hp))
  have hFN := t.contDiffOn_forwardTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))
  have hAN := t.contDiffOn_adjointTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))
  have hTaylor : CoarseAngularFields.SmoothAt t.adjointTaylorAngularFields p :=
    ⟨hA,hF,(fun ij => contDiffAt_relativeAngularDerivative d.γ t.adjointTaylor p hAN hNorm ij.1 ij.2),
      (fun ij => contDiffAt_relativeAngularDerivative d.γ t.forwardTaylor p hFN hNorm ij.1 ij.2)⟩
  exact hTaylor
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
