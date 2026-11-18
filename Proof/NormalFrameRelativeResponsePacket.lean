import Proof.UniformNormalFrameRelativeAdjointHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- One true open-domain response witness, retained by all downstream
    point, adjoint, coframe and higher horizontal consumers. -/
structure NormalFrameRelativeResponsePacket {Y Ω : Set X} {d : Data} {y : X}
    {N : ℕ} {Z C : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C) where
  domain : Set NormalFrameRelativeParameter
  domainOpen : IsOpen domain
  pointMem : ((y,frameVectorLinear d.frame y),0) ∈ domain
  sub : domain ⊆ q.domain
  response : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  smooth : ContDiffOn ℝ ∞ response domain
  highRestriction : ∀ p ∈ domain,(response p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (actualHighRadialErrorL (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))
  oneInvertible : ∀ p ∈ domain,(oneBoundaryCoefficientMulL (normalCoefficientJet
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))).IsInvertible
  adjointSmooth : ContDiffOn ℝ ∞ (fun p => radialAdjointFromResponseL
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p)
      (response p+sphereSobolevDegreeL)) domain

namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

def forwardTaylor (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  t.response p-d.radius y •
    (coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))

def adjointTaylor (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  radialAdjointFromResponseL
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p)
      (t.response p+sphereSobolevDegreeL)-sphereSobolevDegreeL-
    d.radius y • (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num))

theorem contDiffAt_forwardTaylor (t : NormalFrameRelativeResponsePacket q) :
    ContDiffAt ℝ ∞ t.forwardTaylor ((y,frameVectorLinear d.frame y),0) := by
  have hR := t.smooth.contDiffAt (t.domainOpen.mem_nhds t.pointMem)
  have hEll := q.covectorSmooth.contDiffAt (q.domainOpen.mem_nhds q.pointMem)
  have hFirst : ContDiffAt ℝ ∞ (fun p => coarseFirstRadialVariationL 1
      (normalFrameRelativeFirstCovector d.γ d.g₁ p)) ((y,frameVectorLinear d.frame y),0) := by
    have heq : (fun p => coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)) =
        fun p => radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p) := by
      funext p
      simpa only [inv_one,one_smul] using coarseFirstRadialVariationL_normalized_covector 1
        (normalFrameRelativeFirstCovector d.γ d.g₁ p)
    rw [heq]
    exact radialCorrectionCovectorL.contDiff.contDiffAt.comp _ hEll
  exact hR.sub ((hFirst.clm_comp contDiffAt_const).const_smul (d.radius y))

theorem contDiffAt_adjointTaylor (t : NormalFrameRelativeResponsePacket q) :
    ContDiffAt ℝ ∞ t.adjointTaylor ((y,frameVectorLinear d.frame y),0) := by
  have hA := t.adjointSmooth.contDiffAt (t.domainOpen.mem_nhds t.pointMem)
  have hEll := q.covectorSmooth.contDiffAt (q.domainOpen.mem_nhds q.pointMem)
  have hCorr := radialCorrectionCovectorL.contDiff.contDiffAt.comp _ hEll
  let Adj := (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0))
  have hAdj := Adj.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp _ hCorr
  exact (hA.sub contDiffAt_const).sub ((hAdj.clm_comp contDiffAt_const).const_smul (d.radius y))

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
