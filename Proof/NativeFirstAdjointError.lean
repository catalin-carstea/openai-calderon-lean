import Proof.RelativeCoframeSobolevMultiplier
import Proof.RelativeFirstAdjointErrorJets
import Proof.NativeAdjointHalfTaylor
import Proof.NativeCenterGradientHalfFamily
import Proof.FirstAdjointNormalForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
namespace NativeRelativeHorizontalTaylorData

def firstAdjointErrorFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  relativeFirstAdjointErrorOperator (d.radius y) (normalFrameRelativeInverseRadiusFactor p)
    (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a)
    (s.response.adjointTaylor p) (relativeCoframeNormalSobolevL 1 d.γ a p) (s.centerGradientAdjointFamily C p)

def firstAdjointHalfErrorFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  relativeFirstAdjointErrorOperator (d.radius y) (normalFrameRelativeInverseRadiusFactor p)
    (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a)
    (s.response.adjointHalfTaylor p) (relativeCoframeNormalSobolevL (1/2:ℝ) d.γ a p) (s.centerGradientHalfFamily C p)

lemma firstAdjointHalfErrorFamily_coarse_compatible
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (s.firstAdjointErrorFamily C p) =
      (s.firstAdjointHalfErrorFamily C p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply relativeFirstAdjointErrorOperator_compatible
  · exact V.adjointHalfTaylor_coarse_compatible (by norm_num) F0 hF0 p hp
  · apply ContinuousLinearMap.ext
    intro u
    exact relativeCoframeNormalSobolev_inclusion 1 (1/2:ℝ) (by norm_num) d.γ a p u
  · exact s.centerGradientHalfFamily_coarse_compatible C V p hp

lemma adjointTaylor_actual_point
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω) :
    s.response.adjointTaylor ((y,frameVectorLinear d.frame y),0) =
      radialAdjointTaylorRemainderL s.radialAdjointL (firstRadialCorrectionL d y) (d.radius y) := by
  unfold NormalFrameRelativeResponsePacket.adjointTaylor radialAdjointTaylorRemainderL
  rw [h.normalFrameRelativeFirstCovector_actual_zero hΩ hK hy,firstRadialCorrectionL_eq_covector]
  rfl

lemma firstAdjointErrorFamily_actual_point
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    s.firstAdjointErrorFamily C ((y,frameVectorLinear d.frame y),0) =
      firstBoundaryAdjointRemainderL (fixedCenterCoefficient Q d.γ d.frame y a)
        (fun j => (C j).pointCoefficient) s.radialAdjointL (firstRadialCorrectionL d y)
        (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y a) := by
  unfold firstAdjointErrorFamily
  rw [s.adjointTaylor_actual_point hΩ h hK hy,relativeCoframeNormalSobolev_point h hy Q hQ,
    s.centerGradientAdjointFamily_actual]
  simp only [relativeFirstAdjointErrorOperator,normalFrameRelativeInverseRadiusFactor,
    add_zero,inv_one,one_smul,firstBoundaryAdjointRemainderL]
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
