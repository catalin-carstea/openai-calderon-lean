import Proof.BoundaryGradientAdjoint
import Proof.BoundaryGradientRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Boundary gradient operators and their true sphere adjoints only depend
    on the actual coefficient values on the sphere. -/
theorem boundaryGradientL_and_adjoint_congr_sphere
    (F G : I → SmoothCoefficientJets 2)
    (hFG : ∀ j : I,∀ w : UnitSphere,coefficientValue 2 (F j) w.val = coefficientValue 2 (G j) w.val)
    (D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    boundaryGradientL F D = boundaryGradientL G D ∧
      boundaryGradientAdjointL F Da = boundaryGradientAdjointL G Da := by
  have hSphere (j : I) : smoothSphereValue (coefficientSmoothData (F j)) =
      smoothSphereValue (coefficientSmoothData (G j)) := by
    apply ContinuousMap.ext
    intro w
    exact hFG j w
  have hNormal (w : UnitSphere) : coefficientValue 2 (vectorNormalJet F) w.val =
      coefficientValue 2 (vectorNormalJet G) w.val := by
    rw [coefficientValue_vectorNormalJet,coefficientValue_vectorNormalJet]
    change (∑ j : I,w.val j*coefficientValue 2 (F j) w.val) =
      ∑ j : I,w.val j*coefficientValue 2 (G j) w.val
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun c : ℝ => w.val j*c) (hFG j w))
  have hNormalSphere : smoothSphereValue (coefficientSmoothData (vectorNormalJet F)) =
      smoothSphereValue (coefficientSmoothData (vectorNormalJet G)) := by
    apply ContinuousMap.ext
    exact hNormal
  have hNormalOne : oneBoundaryCoefficientMulL (vectorNormalJet F) = oneBoundaryCoefficientMulL (vectorNormalJet G) :=
    oneBoundaryCoefficientMulL_congr_sphere _ _ hNormal
  have hOne (j : I) : oneBoundaryCoefficientMulL (F j) = oneBoundaryCoefficientMulL (G j) :=
    oneBoundaryCoefficientMulL_congr_sphere _ _ (hFG j)
  constructor
  · simp only [boundaryGradientL,coarseBoundaryTangentialL,hSphere,hNormalSphere]
  · simp only [boundaryGradientAdjointL,adjointBoundaryTangentialL,hOne,hNormalOne]

end ShrinkingSpheres
