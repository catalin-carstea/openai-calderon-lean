import Proof.CoordinateBoundaryGradientFields
import Proof.IndexedOperatorRotationProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace CoarseAngularFields
lemma gradient_coordinate_sum (Q : I → ClosedCoefficientJets 3) (P : CoarseAngularFields) :
    (gradient Q P).operator = ∑ k : I,(coordinateGradientAdjoint P k).operator.comp
      (closedOneBoundaryScalarMultiplierL (Q k)) := rfl

lemma gradient_angular_vector_formula (Q : I → ClosedCoefficientJets 3) (P : CoarseAngularFields) (i j : I) :
    (gradient Q P).angular (i,j) =
      (∑ k : I,(coordinateGradientAdjoint P k).operator.comp
        (closedCoefficientAngularOneL i j (Q k)+
          (if k=i then closedOneBoundaryScalarMultiplierL (Q j) else 0)-
          (if k=j then closedOneBoundaryScalarMultiplierL (Q i) else 0)))+
        (P.angular (i,j)).comp (closedVectorNormalMultiplier Q) := by
  change (∑ k : I,(((coordinateGradientAdjoint P k).angular (i,j)).comp
    (closedOneBoundaryScalarMultiplierL (Q k))+
    ((coordinateGradientAdjoint P k).operator).comp (closedCoefficientAngularOneL i j (Q k)))) = _
  simp only [coordinateGradientAdjoint_angular]
  exact indexed_rotation_product_rule
    (fun k => (coordinateGradientAdjoint P k).operator)
    (fun k => closedOneBoundaryScalarMultiplierL (Q k))
    (fun k => closedCoefficientAngularOneL i j (Q k))
    (P.angular (i,j)) oneSphereCoordinateMulL i j
end CoarseAngularFields
end ShrinkingSpheres
