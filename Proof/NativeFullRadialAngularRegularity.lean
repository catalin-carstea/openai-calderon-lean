import Proof.NativeTaylorAngularRegularity
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

lemma fullAdjointAngularFields_smoothAt (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    CoarseAngularFields.SmoothAt t.fullAdjointAngularFields p := by
  have hTaylor := t.adjointTaylorAngularFields_smoothAt V hΩ h hK p hp
  have hEll := q.covectorSmooth.contDiffAt (q.domainOpen.mem_nhds (t.sub (V.sub hp)))
  exact hTaylor.add ((CoarseAngularFields.SmoothAt.constant (CoarseAngularFields.ofPacket degreeCoarseAdjointPacket) p).add
    ((firstRadialAdjointFields_smoothAt hEll).const_smul (d.radius y)))

lemma fullAdjointAngularFields_jet_bound (t : NormalFrameRelativeResponsePacket q)
    (p : NormalFrameRelativeParameter) (J : ℕ) (BT BE : ℝ)
    (hTaylor : CoarseAngularFields.JetBound t.adjointTaylorAngularFields p J BT)
    (hEll : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁) p J BE)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1) :
    CoarseAngularFields.JetBound t.fullAdjointAngularFields p J
      (BT+(CoarseAngularFields.ofPacket degreeCoarseAdjointPacket).budget+firstRadialAngularFieldJetBudget*BE) := by
  have hB : 0 ≤ firstRadialAngularFieldJetBudget*BE := mul_nonneg firstRadialAngularFieldJetBudget_nonneg hEll.nonneg
  have hFirst := (firstRadialAdjointFields_jet_bound hEll).const_smul (d.radius y)
  rw [abs_of_nonneg hr] at hFirst
  have hFirst' := hFirst.weaken ((mul_le_mul_of_nonneg_right hr1 hB).trans_eq (one_mul _))
  have hh := hTaylor.add ((CoarseAngularFields.ofPacket degreeCoarseAdjointPacket).constant_jet_bound p J |>.add hFirst')
  have hFam : t.fullAdjointAngularFields = fun x =>
      (t.adjointTaylorAngularFields x).add ((CoarseAngularFields.ofPacket degreeCoarseAdjointPacket).add
        ((CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket
          (normalFrameRelativeFirstCovector d.γ d.g₁ x))).smul (d.radius y))) := rfl
  rw [hFam]
  simpa only [add_assoc] using hh

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
