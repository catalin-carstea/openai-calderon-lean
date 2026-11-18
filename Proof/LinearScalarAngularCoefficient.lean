import Proof.LinearScalarCoefficient
import Proof.FirstRadialRotationDerivative
import Proof.SmoothScalarRotationDerivative
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

lemma linearScalarClosedCoefficient_angular_coarse (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (ell : X →L[ℝ] ℝ) (i j : I) :
    closedThreeJetCoarseScalarMultiplierL (linearScalarClosedCoefficientL Q (rotationCovector ell i j))=
      closedCoefficientAngularCoarseL i j (linearScalarClosedCoefficientL Q ell) := by
  let P := linearScalarSmoothCoefficient Q ell
  let F := fun θ : ℝ => linearScalarClosedCoefficientL Q
    (ell.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)
  have hD := closedThreeJetCoarseScalarMultiplierL.hasFDerivAt.comp_hasDerivAt (0:ℝ)
    ((linearScalarClosedCoefficientL Q).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      (hasDerivAt_rotated_covector_zero ell i j))
  have hFun : (fun θ => closedThreeJetCoarseScalarMultiplierL (F θ))=
      smoothCoefficientRotatingCoarseFamily P i j := by
    funext θ
    dsimp only [F]
    rw [linearScalarClosedCoefficientL_eq_closure,closedThreeJetCoarseScalarMultiplierL_on_smooth]
    apply congrArg coarseScalarMultiplierMapL
    apply ContinuousMap.ext
    intro w
    let wr : UnitSphere := ⟨coordinateRotationIsometry i j θ w.val,by
      simpa only [Metric.mem_sphere,dist_zero_right,(coordinateRotationIsometry i j θ).norm_map] using w.property⟩
    change coefficientValue 2 (smoothMultiplierLowerJets
      (linearScalarSmoothCoefficient Q (ell.comp (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap))) w.val=
      coefficientValue 2 (smoothMultiplierLowerJets P) wr.val
    rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_smoothMultiplierLowerJets,
      linearScalarSmoothCoefficient_value Q hQ _ w,linearScalarSmoothCoefficient_value Q hQ ell wr]
    rfl
  have hD' : HasDerivAt (fun θ => closedThreeJetCoarseScalarMultiplierL (F θ))
      (closedThreeJetCoarseScalarMultiplierL (linearScalarClosedCoefficientL Q (rotationCovector ell i j))) 0 := hD
  rw [hFun] at hD'
  have hh := hD'.unique (hasDerivAt_smoothCoefficientRotatingCoarseFamily P i j)
  exact hh.trans (congrArg (closedCoefficientAngularCoarseL i j)
    (linearScalarClosedCoefficientL_eq_closure Q ell).symm)

lemma linearScalarClosedCoefficient_angular_half (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (ell : X →L[ℝ] ℝ) (i j : I) :
    closedThreeJetHalfBoundaryScalarMultiplierL (linearScalarClosedCoefficientL Q (rotationCovector ell i j))=
      closedCoefficientAngularHalfL i j (linearScalarClosedCoefficientL Q ell) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_half_scalar_multiplier_coarse,closedCoefficientAngularHalfL_coarse,
    linearScalarClosedCoefficient_angular_coarse Q hQ ell i j]
end ShrinkingSpheres
