import Proof.BoundaryNormalContractionAlgebra
import Proof.LinearScalarCoefficient
import Proof.ClosedNegativeScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic
namespace RelativeNormalScalarRemainderFamily
variable {d : Data} {y : X} {C : ℝ}

def smoothNormalCoefficient (R : RelativeNormalScalarRemainderFamily d y C) (Q : SmoothCoefficientJets 2)
    (p : NormalFrameRelativeParameter) : SmoothCoefficientJets 3 :=
  coefficientThirdJet Q+d.radius y • linearScalarSmoothCoefficient Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)+
    commonSupportCoefficientFamily 3 R.scalar R.smooth R.support R.compact R.supported p

def normalCoefficient (R : RelativeNormalScalarRemainderFamily d y C) (Q : SmoothCoefficientJets 2)
    (p : NormalFrameRelativeParameter) : ClosedCoefficientJets 3 :=
  smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q)+
    d.radius y • linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)+R.closed p

lemma normalCoefficient_eq_closure (R : RelativeNormalScalarRemainderFamily d y C) (Q : SmoothCoefficientJets 2)
    (p : NormalFrameRelativeParameter) :
    R.normalCoefficient Q p=smoothCoefficientClosureInclusionL 3 (R.smoothNormalCoefficient Q p) := by
  simp only [normalCoefficient,smoothNormalCoefficient,map_add,map_smul,linearScalarClosedCoefficientL_eq_closure]
  rfl

lemma smoothNormalCoefficient_point_value (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=normalizedFirstNormalCoefficient d y w.val)
    (w : UnitSphere) :
    coefficientValue 3 (R.smoothNormalCoefficient Q ((y,frameVectorLinear d.frame y),0)) w.val=
      (boundaryNormalCoefficientData F).1 w.val := by
  have hOne : coefficientValue 2 Q w.val=1 := (hQ w.val (Metric.sphere_subset_closedBall w.property)).eq_of_nhds
  simp only [smoothNormalCoefficient,coefficientValue_add,Pi.add_apply,coefficientValue_coefficientThirdJet,
    coefficientValue_smul,Pi.smul_apply,smul_eq_mul,linearScalarSmoothCoefficient_value Q hQ,
    coefficientValue_commonSupportCoefficientFamily,hOne,
    h.normalFrameRelativeFirstCovector_actual_zero hΩ hK hy]
  exact (R.point_scalar_expansion hΩ h hK hy F hF w).symm

lemma normalCoefficient_point_one_multiplier (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=normalizedFirstNormalCoefficient d y w.val) :
    closedOneBoundaryScalarMultiplierL (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))=
      oneBoundaryCoefficientMulL (normalCoefficientJet F) := by
  rw [R.normalCoefficient_eq_closure,closedOneBoundaryScalarMultiplierL_on_smooth]
  apply oneBoundaryCoefficientMulL_congr_sphere
  intro w
  rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_normalCoefficientJet]
  exact R.smoothNormalCoefficient_point_value Q hQ hΩ h hK hy F hF w

lemma normalCoefficient_point_coarse_multiplier (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=normalizedFirstNormalCoefficient d y w.val) :
    closedThreeJetCoarseScalarMultiplierL (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))=
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))) := by
  rw [R.normalCoefficient_eq_closure,closedThreeJetCoarseScalarMultiplierL_on_smooth]
  apply congrArg coarseSphereScalarMulL
  apply ContinuousMap.ext
  intro w
  change coefficientValue 2 (smoothMultiplierLowerJets
    (R.smoothNormalCoefficient Q ((y,frameVectorLinear d.frame y),0))) w.val=
      coefficientValue 2 (normalCoefficientJet F) w.val
  rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_normalCoefficientJet]
  exact R.smoothNormalCoefficient_point_value Q hQ hΩ h hK hy F hF w

lemma normalCoefficient_point_negative_multiplier (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=normalizedFirstNormalCoefficient d y w.val) :
    closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))=
      negativeBoundaryCoefficientMulL (normalCoefficientJet F) := by
  rw [R.normalCoefficient_eq_closure]
  change (closedThreeJetHalfBoundaryScalarMultiplierL
    (smoothCoefficientClosureInclusionL 3 (R.smoothNormalCoefficient Q ((y,frameVectorLinear d.frame y),0)))).adjoint=_
  rw [closedThreeJetHalfBoundaryScalarMultiplierL_on_smooth]
  apply congrArg ContinuousLinearMap.adjoint
  apply halfBoundaryCoefficientMulL_congr_sphere
  intro w
  rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_normalCoefficientJet]
  exact R.smoothNormalCoefficient_point_value Q hQ hΩ h hK hy F hF w
end RelativeNormalScalarRemainderFamily
end ShrinkingSpheres
