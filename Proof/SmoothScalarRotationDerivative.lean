import Proof.Archive.NativeSmoothSphereRotationAngleDerivative
import Proof.ClosedCoefficientAngularGenerators
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
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

def smoothCoefficientRotatingCoarseFamily (Q : SmoothCoefficientJets 3) (i j : I) :
    ℝ → SphereSobolev 0 →L[ℝ] SphereSobolev 0 := fun θ =>
  coarseScalarMultiplierMapL (coordinateRotationSphereSection i j
    (coefficientSmoothData (smoothMultiplierLowerJets Q)).1
    (coefficientSmoothData (smoothMultiplierLowerJets Q)).2 θ)

lemma smoothCoefficientRotatingCoarseFamily_zero (Q : SmoothCoefficientJets 3) (i j : I) :
    smoothCoefficientRotatingCoarseFamily Q i j 0 =
      closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q) := by
  rw [closedThreeJetCoarseScalarMultiplierL_on_smooth]
  unfold smoothCoefficientRotatingCoarseFamily
  rw [coordinateRotationSphereSection_zero]
  rfl

lemma hasDerivAt_smoothCoefficientRotatingCoarseFamily (Q : SmoothCoefficientJets 3) (i j : I) :
    HasDerivAt (smoothCoefficientRotatingCoarseFamily Q i j)
      (closedCoefficientAngularCoarseL i j (smoothCoefficientClosureInclusionL 3 Q)) 0 := by
  let D := coefficientSmoothData (smoothMultiplierLowerJets Q)
  have hR := hasDerivAt_coordinateRotationSphereSection i j D.1 D.2 0
  rw [coordinateRotationSphereSection_zero] at hR
  have hM := coarseScalarMultiplierMapL.hasFDerivAt.comp_hasDerivAt (0:ℝ) hR
  have hValue : OAI.AnisotropicCalderon.SmoothAngularCasimir.smoothSphereRestriction
      (sphereRotationDerivative i j D.1) (contDiff_sphereRotationDerivative i j D.1 D.2) =
        smoothSphereValue (smoothRotationData i j D) := rfl
  rw [hValue] at hM
  rw [closedCoefficientAngularCoarseL_on_smooth]
  exact hM
end ShrinkingSpheres
