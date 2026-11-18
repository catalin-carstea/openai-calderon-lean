import Proof.NativeFirstErrorAngularFields
import Proof.FirstErrorAngularJetBounds
import Proof.SmoothFiniteJetApply
import Proof.NativeCenterGradientAngularJets
import Proof.ScaledNormalFrameHorizontalInputJets
import Proof.RelativeInverseRadiusFactorJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma NativeRelativeHorizontalTaylorData.firstErrorAngularFields_scaled_three_jets
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (β BR BP BQ BL BD : ℝ) (hr : 0 < d.radius y) (hβ : 1 ≤ β)
    (hrβ : d.radius y*β ≤ 1) (hBR : 0 ≤ BR) (hBP : 0 ≤ BP)
    (hBQ : 0 ≤ BQ) (hBL : 0 ≤ BL) (hBD : 0 ≤ BD) (hCC : 0 ≤ CC)
    (hP : CoarseAngularFields.JetBound s.response.adjointTaylorAngularFields
      ((y,frameVectorLinear d.frame y),0) 3 (BP*(d.radius y)^2))
    (hD : CoarseAngularFields.JetBound s.response.fullAdjointAngularFields
      ((y,frameVectorLinear d.frame y),0) 3 BD)
    (hQ : ∀ j,SmoothFiniteJetBound (normalFrameRelativeCoframeValue d.γ a j)
      ((y,frameVectorLinear d.frame y),0) 3 (BQ*‖a‖))
    (hR : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor
      ((y,frameVectorLinear d.frame y),0) 3 BR)
    (hRs : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor
      ((0,frameVectorLinear d.frame y),0) 3 BR)
    (hLog : SmoothFiniteJetBound (normalFrameScaledLogCovector d.radius β y)
      ((0,frameVectorLinear d.frame y),0) 3 BL) :
    CoarseAngularFields.JetBound (s.firstErrorAngularFields C ∘ normalFrameRelativeScaledParameter β y)
      ((0,frameVectorLinear d.frame y),0) 3
      (firstErrorAngularJetBudget BR (6*BP) (6*BQ) BL
        (6*(2^3*BR*boundaryGradientAngularJetBudget 3 BD*CC))*‖a‖*d.radius y) := by
  let p0 : NormalFrameRelativeParameter := ((0,frameVectorLinear d.frame y),0)
  let Φ := normalFrameRelativeScaledParameter β y
  let BG := 2^3*BR*boundaryGradientAngularJetBudget 3 BD*CC
  have hBG : 0 ≤ BG := by
    have hGrad := boundaryGradientAngularJetBudget_nonneg 3 hBD
    dsimp only [BG]
    positivity
  have hPs : CoarseAngularFields.JetBound (s.response.adjointTaylorAngularFields ∘ Φ) p0 3
      ((6*BP)*(d.radius y)^2) := by
    simpa only [mul_assoc] using hP.scaled_parameter_three hβ
  have hQs (j : I) : SmoothFiniteJetBound (normalFrameRelativeCoframeValue d.γ a j ∘ Φ) p0 3
      ((6*BQ)*‖a‖) := by
    simpa only [mul_assoc] using normalFrame_scaled_parameter_three_jet_bound β hβ y
      (frameVectorLinear d.frame y) (hQ j)
  have hG := s.centerGradientAngularFields_jet_bound C BD BR hCC hr hD hR
  have hGs : CoarseAngularFields.JetBound (s.centerGradientAngularFields C ∘ Φ) p0 3
      ((6*BG)*‖a‖*d.radius y) := by
    simpa only [BG,mul_assoc] using hG.scaled_parameter_three hβ
  have hb := hLog.apply_const a
  have hBound := firstError_angular_scaled_three_jet_bound hr hβ hrβ (norm_nonneg a)
    hBR (mul_nonneg (by norm_num) hBP) (mul_nonneg (by norm_num) hBQ) hBL
    (mul_nonneg (by norm_num) hBG) hPs hQs hRs hb hGs
  have hβ0 : β ≠ 0 := (zero_lt_one.trans_le hβ).ne'
  have hEq : (fun p =>
      (((((s.response.adjointTaylorAngularFields (Φ p)).mulCoordinateCombination
        (fun j => (normalFrameRelativeCoframeValue d.γ a j ∘ Φ) p)).smul
        (normalFrameRelativeInverseRadiusFactor p)).smul (d.radius y)⁻¹).add
        ((s.response.adjointTaylorAngularFields (Φ p)).smul
          (β*(normalFrameScaledLogCovector d.radius β y p a)))).add
          (s.centerGradientAngularFields C (Φ p))) = (s.firstErrorAngularFields C ∘ Φ) := by
    funext p
    have hbEq : β*normalFrameScaledLogCovector d.radius β y p a =
        fderiv ℝ (fun x => Real.log (d.radius x)) (Φ p).1.1 a := by
      change β*(β⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) (normalFrameScaledCenter β y p) a) = _
      rw [← mul_assoc,mul_inv_cancel₀ hβ0,one_mul]
      rfl
    rw [hbEq]
    rfl
  change CoarseAngularFields.JetBound (fun p =>
      (((((s.response.adjointTaylorAngularFields (Φ p)).mulCoordinateCombination
        (fun j => (normalFrameRelativeCoframeValue d.γ a j ∘ Φ) p)).smul
        (normalFrameRelativeInverseRadiusFactor p)).smul (d.radius y)⁻¹).add
        ((s.response.adjointTaylorAngularFields (Φ p)).smul
          (β*(normalFrameScaledLogCovector d.radius β y p a)))).add
          (s.centerGradientAngularFields C (Φ p))) p0 3 _ at hBound
  rw [hEq] at hBound
  exact hBound
end ShrinkingSpheres
