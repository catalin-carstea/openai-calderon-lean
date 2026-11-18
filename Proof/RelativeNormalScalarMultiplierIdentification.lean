import Proof.CompletedNormalCoefficientFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
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
lemma scalar_expansion_at_parameter (R : RelativeNormalScalarRemainderFamily d y C)
    (p : NormalFrameRelativeParameter) (hp : p ∈ R.domain) (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=
      normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,w.val)) (w : UnitSphere) :
    (boundaryNormalCoefficientData F).1 w.val=
      1+d.radius y*normalFrameRelativeFirstCovector d.γ d.g₁ p w.val+R.scalar (p,w.val) := by
  have hw : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num)
    (Metric.sphere_subset_closedBall w.property)
  have hR := (R.actual p hp w.val hw).eq_of_nhds
  change R.scalar (p,w.val)=matrixNormalContraction
    (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,w.val)-(1:Mat)-
      d.radius y • normalFrameRelativeFirstModel d.γ d.g₁ (p,w.val)) w.val at hR
  rw [normalFrameRelativeFirstModel_scalar,← hF w,matrixNormalContraction_sub,matrixNormalContraction_sub,
    matrixNormalContraction_normal_data,matrixNormalContraction_one,matrixNormalContraction_smul,
    matrixNormalContraction_smul,matrixNormalContraction_one,mul_one] at hR
  linarith only [hR]
lemma smoothNormalCoefficient_value_at_parameter (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (p : NormalFrameRelativeParameter) (hp : p ∈ R.domain) (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=
      normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,w.val)) (w : UnitSphere) :
    coefficientValue 3 (R.smoothNormalCoefficient Q p) w.val=(boundaryNormalCoefficientData F).1 w.val := by
  have hOne : coefficientValue 2 Q w.val=1 := (hQ w.val (Metric.sphere_subset_closedBall w.property)).eq_of_nhds
  simp only [smoothNormalCoefficient,coefficientValue_add,Pi.add_apply,coefficientValue_coefficientThirdJet,
    coefficientValue_smul,Pi.smul_apply,smul_eq_mul,linearScalarSmoothCoefficient_value Q hQ,
    coefficientValue_commonSupportCoefficientFamily,hOne]
  exact (R.scalar_expansion_at_parameter p hp F hF w).symm
lemma normalCoefficient_one_multiplier_at_parameter (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (p : NormalFrameRelativeParameter) (hp : p ∈ R.domain) (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=
      normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,w.val)) :
    closedOneBoundaryScalarMultiplierL (R.normalCoefficient Q p)=oneBoundaryCoefficientMulL (normalCoefficientJet F) := by
  rw [R.normalCoefficient_eq_closure,closedOneBoundaryScalarMultiplierL_on_smooth]
  apply oneBoundaryCoefficientMulL_congr_sphere
  intro w
  rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_normalCoefficientJet]
  exact R.smoothNormalCoefficient_value_at_parameter Q hQ p hp F hF w
lemma normalCoefficient_coarse_multiplier_at_parameter (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (p : NormalFrameRelativeParameter) (hp : p ∈ R.domain) (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=
      normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,w.val)) :
    closedThreeJetCoarseScalarMultiplierL (R.normalCoefficient Q p)=
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))) := by
  rw [R.normalCoefficient_eq_closure,closedThreeJetCoarseScalarMultiplierL_on_smooth]
  apply congrArg coarseSphereScalarMulL
  apply ContinuousMap.ext
  intro w
  change coefficientValue 2 (smoothMultiplierLowerJets (R.smoothNormalCoefficient Q p)) w.val=
    coefficientValue 2 (normalCoefficientJet F) w.val
  rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_normalCoefficientJet]
  exact R.smoothNormalCoefficient_value_at_parameter Q hQ p hp F hF w
lemma normalCoefficient_negative_multiplier_at_parameter (R : RelativeNormalScalarRemainderFamily d y C)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (p : NormalFrameRelativeParameter) (hp : p ∈ R.domain) (F : SmoothCoefficientMatrix 2)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val=
      normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,w.val)) :
    closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)=negativeBoundaryCoefficientMulL (normalCoefficientJet F) := by
  rw [R.normalCoefficient_eq_closure]
  change (closedThreeJetHalfBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 (R.smoothNormalCoefficient Q p))).adjoint=_
  rw [closedThreeJetHalfBoundaryScalarMultiplierL_on_smooth]
  apply congrArg ContinuousLinearMap.adjoint
  apply halfBoundaryCoefficientMulL_congr_sphere
  intro w
  rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_normalCoefficientJet]
  exact R.smoothNormalCoefficient_value_at_parameter Q hQ p hp F hF w
end RelativeNormalScalarRemainderFamily
end ShrinkingSpheres
