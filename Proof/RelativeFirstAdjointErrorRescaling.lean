import Proof.RelativeFirstAdjointErrorJets
import Proof.SmoothFiniteJetApply
import Proof.NormalFrameScaledJetBounds
import Proof.ScaledNormalFrameHorizontalInputJets
import Proof.RelativeInverseRadiusFactorJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def firstAdjointErrorScaledJetBudget (BR BP BM BL BG : ℝ) : ℝ :=
  2^3*BR*(2^3*(6*BP)*(6*BM))+2^3*BL*(6*BP)+6*BG

lemma firstAdjointErrorScaledJetBudget_nonneg (BR BP BM BL BG : ℝ)
    (hBR : 0 ≤ BR) (hBP : 0 ≤ BP) (hBM : 0 ≤ BM) (hBL : 0 ≤ BL) (hBG : 0 ≤ BG) :
    0 ≤ firstAdjointErrorScaledJetBudget BR BP BM BL BG := by
  unfold firstAdjointErrorScaledJetBudget
  positivity

/-- Rescaling precedes multiplication by the logarithmic-radius coefficient,
    so its derivatives consume exactly their allowed powers of beta. -/
lemma relativeFirstAdjointError_rescaled_composition_three_jets
    (d : Data) (y a : X) (β BR BP BM BL BG : ℝ)
    (hr : 0 < d.radius y) (hβ : 1 ≤ β) (hrβ : d.radius y*β ≤ 1)
    (hBR : 0 ≤ BR) (hBP : 0 ≤ BP) (hBM : 0 ≤ BM) (hBL : 0 ≤ BL) (hBG : 0 ≤ BG)
    (A G : NormalFrameRelativeParameter → E →L[ℝ] F)
    (M : NormalFrameRelativeParameter → E →L[ℝ] E)
    (hA : SmoothFiniteJetBound A ((y,frameVectorLinear d.frame y),0) 3 (BP*(d.radius y)^2))
    (hM : SmoothFiniteJetBound M ((y,frameVectorLinear d.frame y),0) 3 (BM*‖a‖))
    (hG : SmoothFiniteJetBound G ((y,frameVectorLinear d.frame y),0) 3 (BG*‖a‖*d.radius y))
    (hR : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor ((0,frameVectorLinear d.frame y),0) 3 BR)
    (hLog : SmoothFiniteJetBound (normalFrameScaledLogCovector d.radius β y)
      ((0,frameVectorLinear d.frame y),0) 3 BL) :
    SmoothFiniteJetBound ((fun p => relativeFirstAdjointErrorOperator (d.radius y)
      (normalFrameRelativeInverseRadiusFactor p) (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a)
      (A p) (M p) (G p)) ∘ normalFrameRelativeScaledParameter β y)
      ((0,frameVectorLinear d.frame y),0) 3
      (firstAdjointErrorScaledJetBudget BR BP BM BL BG*‖a‖*d.radius y) := by
  let p0 : NormalFrameRelativeParameter := ((0,frameVectorLinear d.frame y),0)
  let Φ := normalFrameRelativeScaledParameter β y
  have hb := hLog.apply_const a
  have hAs : SmoothFiniteJetBound (A ∘ Φ) p0 3 ((6*BP)*(d.radius y)^2) := by
    simpa only [mul_assoc] using normalFrame_scaled_parameter_three_jet_bound β hβ y (frameVectorLinear d.frame y) hA
  have hMs : SmoothFiniteJetBound (M ∘ Φ) p0 3 ((6*BM)*‖a‖) := by
    simpa only [mul_assoc] using normalFrame_scaled_parameter_three_jet_bound β hβ y (frameVectorLinear d.frame y) hM
  have hGs : SmoothFiniteJetBound (G ∘ Φ) p0 3 ((6*BG)*‖a‖*d.radius y) := by
    simpa only [mul_assoc] using normalFrame_scaled_parameter_three_jet_bound β hβ y (frameVectorLinear d.frame y) hG
  have hRs : SmoothFiniteJetBound (normalFrameRelativeInverseRadiusFactor ∘ Φ) p0 3 BR := hR
  have hBound := relativeFirstAdjointError_scaled_three_jet_bound hr hβ hrβ (norm_nonneg a)
    hBR (mul_nonneg (by norm_num) hBP) (mul_nonneg (by norm_num) hBM) hBL (mul_nonneg (by norm_num) hBG)
    hRs hAs hMs hb hGs
  have hβ0 : β ≠ 0 := (zero_lt_one.trans_le hβ).ne'
  have hEq : (fun p => relativeFirstAdjointErrorOperator (d.radius y)
      ((normalFrameRelativeInverseRadiusFactor ∘ Φ) p)
      (β*(normalFrameScaledLogCovector d.radius β y p a)) ((A ∘ Φ) p) ((M ∘ Φ) p) ((G ∘ Φ) p)) =
      ((fun p => relativeFirstAdjointErrorOperator (d.radius y)
        (normalFrameRelativeInverseRadiusFactor p) (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a)
        (A p) (M p) (G p)) ∘ Φ) := by
    funext p
    change relativeFirstAdjointErrorOperator (d.radius y) _
      (β*(β⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) (normalFrameScaledCenter β y p) a)) _ _ _ = _
    rw [← mul_assoc,mul_inv_cancel₀ hβ0,one_mul]
    rfl
  rw [hEq] at hBound
  exact hBound
end ShrinkingSpheres
