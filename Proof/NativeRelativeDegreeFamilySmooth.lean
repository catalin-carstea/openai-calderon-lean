import Proof.NativeRelativeDegreeCompatibleFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
lemma contDiffAt_coarseDegreeDataAssembly
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G H : I × I → P → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (p : P)
    (hF : ContDiffAt ℝ ∞ F p) (hG : ∀ ij,ContDiffAt ℝ ∞ (G ij) p)
    (hH : ∀ ij,ContDiffAt ℝ ∞ (H ij) p) :
    ContDiffAt ℝ ∞ (fun x => (F x,((fun ij => G ij x),(fun ij => H ij x))) :
      P → CoarseDegreeCompatibility.CoarseDegreeData) p := by
  exact hF.prodMk ((contDiffAt_pi.mpr hG).prodMk (contDiffAt_pi.mpr hH))
end ShrinkingSpheres

namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem SymmetricAdjointDomain.contDiffOn_degreeData {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    ContDiffOn ℝ ∞ t.degreeData V.domain := by
  intro p hp
  unfold degreeData
  have hpN := V.normalizationStable p hp
  have hQ : ContDiffAt ℝ ∞ (normalFrameRelativeNormalization d.γ) p :=
    (h.contDiffOn_normalFrameRelativeNormalization hΩ hK).contDiffAt
      ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds (q.positive (t.sub (V.sub hp))))
  have hF := t.contDiffOn_forwardTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hp))
  have hFN := t.contDiffOn_forwardTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))
  have hAN := t.contDiffOn_adjointTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))
  exact (contDiffAt_coarseDegreeDataAssembly t.forwardTaylor
    (fun ij => normalFrameRelativeAngularDerivative d.γ t.forwardTaylor ij.1 ij.2)
    (fun ij => normalFrameRelativeAngularDerivative d.γ t.adjointTaylor ij.1 ij.2)
    p hF (fun ij => contDiffAt_relativeAngularDerivative d.γ t.forwardTaylor p hFN hQ ij.1 ij.2)
    (fun ij => contDiffAt_relativeAngularDerivative d.γ t.adjointTaylor p hAN hQ ij.1 ij.2)).contDiffWithinAt

end ShrinkingSpheres.NormalFrameRelativeResponsePacket
