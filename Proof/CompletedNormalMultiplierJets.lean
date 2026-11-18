import Proof.CompletedNormalCoefficientJets
import Proof.ConjugationCancellationFiniteJets
import Proof.ClosedScalarIdentity
import Proof.NearIdentityInverse
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace RelativeNormalScalarRemainderFamily
variable {d : Data} {y : X} {C BL : ℝ}
lemma normalCoefficient_three_jets (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2) (hC : 0 ≤ C) (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hEll : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁)
      ((y,frameVectorLinear d.frame y),0) 3 BL) :
    SmoothFiniteJetBound (R.normalCoefficient Q) ((y,frameVectorLinear d.frame y),0) 3
      (‖smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q)‖+‖linearScalarClosedCoefficientL Q‖*BL+C) := by
  have hSmall := R.normalCoefficient_small_three_jets Q hC hr hr1 hEll
  have hAdd := hSmall.add (SmoothFiniteJetBound.constant
    (smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q)) ((y,frameVectorLinear d.frame y),0) 3)
  have hEq : (fun p => (R.normalCoefficient Q p-smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q))+
      smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q))=R.normalCoefficient Q := by
    funext p
    exact sub_add_cancel _ _
  have h := hAdd.congr_germ (Filter.Eventually.of_forall (congrFun hEq))
  have hL := hEll.nonneg
  apply h.weaken
  have hB : 0 ≤ ‖linearScalarClosedCoefficientL Q‖*BL+C := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hr1 hB]

lemma normalNegative_small_three_jets (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (hC : 0 ≤ C) (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hEll : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁)
      ((y,frameVectorLinear d.frame y),0) 3 BL) :
    SmoothFiniteJetBound (fun p => closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)-
      ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) ((y,frameVectorLinear d.frame y),0) 3
      ((‖closedThreeJetNegativeScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*BL+C))*d.radius y) := by
  have hOne := smooth_unit_closed_scalar_one (coefficientThirdJet Q) (fun w => by
    rw [coefficientValue_coefficientThirdJet]
    exact (hQ w.val (Metric.sphere_subset_closedBall w.property)).eq_of_nhds)
  have hUnit := (closed_scalar_identity_of_one _ hOne).2
  have h := (R.normalCoefficient_small_three_jets Q hC hr hr1 hEll).clm closedThreeJetNegativeScalarMultiplierL
  have hFam : (fun p => closedThreeJetNegativeScalarMultiplierL
      (R.normalCoefficient Q p-smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q)))=
      (fun p => closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)-
        ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) := by
    funext p
    rw [map_sub,hUnit]
  have hh := h.congr_germ (Filter.Eventually.of_forall (congrFun hFam))
  exact hh.weaken (le_of_eq (by ring))
end RelativeNormalScalarRemainderFamily
end ShrinkingSpheres
