import Proof.SmoothScalarRotationDerivative
import Proof.RelativeAngularDerivativeCurve
import Proof.FixedGeneratorScalarCommutators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

lemma commonSupportClosedCoefficient_angular_coarse (g : MetricField)
    (f : NormalFrameRelativeParameter × X → ℝ) (hf : ContDiff ℝ ∞ f)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → f (p,z)=0)
    (p : NormalFrameRelativeParameter) (i j : I)
    (hRot : ∀ᶠ θ : ℝ in 𝓝 0,∀ w : UnitSphere,
      f (normalFrameRelativeAngularCurve g p i j θ,w.val)=f (p,coordinateRotationIsometry i j θ w.val)) :
    closedThreeJetCoarseScalarMultiplierL
      (normalFrameRelativeAngularDerivative g (commonSupportClosedCoefficientFamily 3 f hf S hS hz) i j p)=
    closedCoefficientAngularCoarseL i j (commonSupportClosedCoefficientFamily 3 f hf S hS hz p) := by
  let F := commonSupportClosedCoefficientFamily 3 f hf S hS hz
  let P := commonSupportCoefficientFamily 3 f hf S hS hz p
  have hF : ContDiff ℝ ∞ F := contDiff_commonSupportClosedCoefficientFamily 3 f hf S hS hz
  have hEq : (fun θ => closedThreeJetCoarseScalarMultiplierL (F (normalFrameRelativeAngularCurve g p i j θ))) =ᶠ[𝓝 (0:ℝ)]
      smoothCoefficientRotatingCoarseFamily P i j := by
    filter_upwards [hRot] with θ hθ
    change closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3
      (commonSupportCoefficientFamily 3 f hf S hS hz (normalFrameRelativeAngularCurve g p i j θ)))=_
    rw [closedThreeJetCoarseScalarMultiplierL_on_smooth]
    apply congrArg coarseScalarMultiplierMapL
    apply ContinuousMap.ext
    intro w
    change coefficientValue 2 (smoothMultiplierLowerJets
      (commonSupportCoefficientFamily 3 f hf S hS hz (normalFrameRelativeAngularCurve g p i j θ))) w.val=
      coefficientValue 2 (smoothMultiplierLowerJets P) (coordinateRotationIsometry i j θ w.val)
    simp only [coefficientValue_smoothMultiplierLowerJets,P,coefficientValue_commonSupportCoefficientFamily]
    exact hθ w
  have hLeft := closedThreeJetCoarseScalarMultiplierL.hasFDerivAt.comp_hasDerivAt (0:ℝ)
    (hasDerivAt_relativeAngularFamily g F p i j (hF.differentiable (by simp) _))
  have hRight := (hasDerivAt_smoothCoefficientRotatingCoarseFamily P i j).congr_of_eventuallyEq hEq
  exact hLeft.unique hRight

lemma commonSupportClosedCoefficient_angular_half (g : MetricField)
    (f : NormalFrameRelativeParameter × X → ℝ) (hf : ContDiff ℝ ∞ f)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → f (p,z)=0)
    (p : NormalFrameRelativeParameter) (i j : I)
    (hRot : ∀ᶠ θ : ℝ in 𝓝 0,∀ w : UnitSphere,
      f (normalFrameRelativeAngularCurve g p i j θ,w.val)=f (p,coordinateRotationIsometry i j θ w.val)) :
    closedThreeJetHalfBoundaryScalarMultiplierL
      (normalFrameRelativeAngularDerivative g (commonSupportClosedCoefficientFamily 3 f hf S hS hz) i j p)=
    closedCoefficientAngularHalfL i j (commonSupportClosedCoefficientFamily 3 f hf S hS hz p) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_half_scalar_multiplier_coarse,closedCoefficientAngularHalfL_coarse,
    commonSupportClosedCoefficient_angular_coarse g f hf S hS hz p i j hRot]
end ShrinkingSpheres
