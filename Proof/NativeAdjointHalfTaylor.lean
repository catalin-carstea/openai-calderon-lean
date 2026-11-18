import Proof.NativeHalfTaylorCompatibility
import Proof.HalfPhysicalAdjoint
import Proof.NativeFullHalfResponse
import Proof.SmoothFiniteAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 1800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

def adjointHalfTaylor (_t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (q.halfTaylor p).adjoint

lemma SymmetricAdjointDomain.adjointHalfTaylor_physical_block
    {t : NormalFrameRelativeResponsePacket q} (V : t.SymmetricAdjointDomain)
    (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (t.adjointHalfTaylor p (sphereSobolevSingleL (1/2:ℝ) n z)) =
      coarsePhysicalHarmonicBlock (t.adjointTaylor p) m n z :=
  half_operator_adjoint_physical_block (t.forwardTaylor p) (t.adjointTaylor p)
    (V.taylorPair p hp) (q.halfTaylor p) (V.halfTaylor_physical_block hZ F0 hF0 p hp) m n z

lemma SymmetricAdjointDomain.adjointHalfTaylor_coarse_compatible
    {t : NormalFrameRelativeResponsePacket q} (V : t.SymmetricAdjointDomain)
    (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (t.adjointTaylor p) =
      (t.adjointHalfTaylor p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) :=
  half_coarse_compatible_of_physical_blocks _ _ (V.adjointHalfTaylor_physical_block hZ F0 hF0 p hp)

lemma SymmetricAdjointDomain.contDiffOn_adjointHalfTaylor
    {t : NormalFrameRelativeResponsePacket q} (V : t.SymmetricAdjointDomain) :
    ContDiffOn ℝ ∞ t.adjointHalfTaylor V.domain := by
  let Adj := (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) ≃ₗᵢ[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))).toContinuousLinearEquiv.toContinuousLinearMap
  exact Adj.contDiff.comp_contDiffOn V.contDiffOn_halfTaylor
end ShrinkingSpheres.NormalFrameRelativeResponsePacket
