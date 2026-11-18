import Proof.CoordinateRotationGenerator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.MetricOperator

/-- Shared genuine operator-norm derivative of a coordinate rotation.
    Extracted from the first radial covector rotation argument. -/
theorem hasDerivAt_coordinateRotationOperator_zero (i j : I) :
    HasDerivAt (fun θ => (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)
      (rotationVectorL i j) 0 := by
  have h := matrixOperatorMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_coordinateRotationMatrix_zero i j)
  have hFun : (fun θ => matrixOperatorMap (coordinateRotationMatrix i j θ)) =
      fun θ => (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap := by
    funext θ
    exact matrixOperatorAlgEquiv.apply_symm_apply _
  have hGen : matrixOperatorMap (coordinateRotationGeneratorMatrix i j) = rotationVectorL i j :=
    matrixOperatorAlgEquiv.apply_symm_apply _
  simpa only [Function.comp_def,hFun,hGen] using h

end ShrinkingSpheres
