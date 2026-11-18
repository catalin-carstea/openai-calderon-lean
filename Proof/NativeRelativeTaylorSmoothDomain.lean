import Proof.NormalFrameRelativeResponseNormalization
import Proof.MidpointRadialAdjointOneInverse
import Proof.CommonSupportMidpointNeighborhood
import Proof.RadialTaylorTrueAdjointPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

theorem contDiffOn_forwardTaylor (t : NormalFrameRelativeResponsePacket q) :
    ContDiffOn ℝ ∞ t.forwardTaylor t.domain := by
  have hCorr := radialCorrectionCovectorL.contDiff.comp_contDiffOn (q.covectorSmooth.mono t.sub)
  have hFirst : ContDiffOn ℝ ∞ (fun p => coarseFirstRadialVariationL 1
      (normalFrameRelativeFirstCovector d.γ d.g₁ p)) t.domain := by
    apply hCorr.congr
    intro p hp
    simpa only [Function.comp_def,inv_one,one_smul] using coarseFirstRadialVariationL_normalized_covector 1
      (normalFrameRelativeFirstCovector d.γ d.g₁ p)
  change ContDiffOn ℝ ∞ (fun p => t.response p-d.radius y •
    (coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))) t.domain
  exact t.smooth.sub ((hFirst.clm_comp contDiffOn_const).const_smul (d.radius y))

theorem contDiffOn_adjointTaylor (t : NormalFrameRelativeResponsePacket q) :
    ContDiffOn ℝ ∞ t.adjointTaylor t.domain := by
  have hCorr := radialCorrectionCovectorL.contDiff.comp_contDiffOn (q.covectorSmooth.mono t.sub)
  let Adj := (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0))
  have hAdj := Adj.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hCorr
  exact (t.adjointSmooth.sub contDiffOn_const).sub
    ((hAdj.clm_comp contDiffOn_const).const_smul (d.radius y))


end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
