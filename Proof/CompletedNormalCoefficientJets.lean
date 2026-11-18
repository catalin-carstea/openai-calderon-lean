import Proof.CompletedNormalCoefficientFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
namespace RelativeNormalScalarRemainderFamily
variable {d : Data} {y : X} {C BL : ℝ}

lemma normalCoefficient_small_three_jets (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2) (hC : 0 ≤ C) (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hEll : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁)
      ((y,frameVectorLinear d.frame y),0) 3 BL) :
    SmoothFiniteJetBound (fun p => R.normalCoefficient Q p-
      smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q))
      ((y,frameVectorLinear d.frame y),0) 3 ((‖linearScalarClosedCoefficientL Q‖*BL+C)*d.radius y) := by
  have hL := (hEll.clm (linearScalarClosedCoefficientL Q)).const_smul (d.radius y)
  rw [abs_of_nonneg hr] at hL
  have hSum := hL.add R.jets
  have hFam : (fun p => R.normalCoefficient Q p-smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q))=
      (fun p => d.radius y • linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)+R.closed p) := by
    funext p
    unfold normalCoefficient
    abel
  rw [hFam]
  apply hSum.weaken
  have hh : C*(d.radius y)^2 ≤ C*d.radius y :=
    mul_le_mul_of_nonneg_left (by nlinarith only [mul_le_mul_of_nonneg_left hr1 hr]) hC
  nlinarith only [hh]
end RelativeNormalScalarRemainderFamily
end ShrinkingSpheres
