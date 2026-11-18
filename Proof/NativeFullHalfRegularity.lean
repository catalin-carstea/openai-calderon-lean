import Proof.NativeFullHalfResponse
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}
  {t : NormalFrameRelativeResponsePacket q}
lemma SymmetricAdjointDomain.contDiffOn_fullHalfResponse (V : t.SymmetricAdjointDomain) :
    ContDiffOn ℝ ∞ t.fullHalfResponse V.domain := by
  have hWeak (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
      (commonSupportZeroWeakEnergy q.a q.smooth p).IsInvertible :=
    isInvertible_of_bilinear_coercive _ (V.coercive p hp)
  exact (contDiffOn_commonSupportLowRadialErrorL q.a q.smooth q.support q.compact q.supported V.domain
    hWeak V.normal).add contDiffOn_const
lemma SymmetricAdjointDomain.contDiffOn_fullHalfAdjoint (V : t.SymmetricAdjointDomain) :
    ContDiffOn ℝ ∞ t.fullHalfAdjoint V.domain := by
  let A := (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) ≃ₗᵢ[ℝ]
      (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (1/2:ℝ))).toContinuousLinearEquiv.toContinuousLinearMap
  exact A.contDiff.comp_contDiffOn V.contDiffOn_fullHalfResponse
end ShrinkingSpheres.NormalFrameRelativeResponsePacket
