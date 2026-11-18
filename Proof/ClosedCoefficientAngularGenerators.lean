import Proof.ClosedCoefficientDirectionalDerivative
import Proof.ClosedTwoJetCoarseScalarMultiplier
import Proof.ClosedThreeJetCoarseScalarMultiplier
import Proof.ClosedBoundaryGradientAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

def closedCoefficientAngularOneL (i j : I) : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 1) :=
  (ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 1) (SphereSobolev 1) (oneSphereCoordinateMulL i)).comp
    (closedTwoJetOneBoundaryScalarMultiplierL.comp (closedCoefficientDirectionalDerivativeL 2 (axis j)))-
  (ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 1) (SphereSobolev 1) (oneSphereCoordinateMulL j)).comp
    (closedTwoJetOneBoundaryScalarMultiplierL.comp (closedCoefficientDirectionalDerivativeL 2 (axis i)))

def closedCoefficientAngularCoarseL (i j : I) : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
  (ContinuousLinearMap.compL ℝ (SphereSobolev 0) (SphereSobolev 0) (SphereSobolev 0)
    (coarseSphereScalarMulL (sphereCoordinate i))).comp
      (closedTwoJetCoarseScalarMultiplierL.comp (closedCoefficientDirectionalDerivativeL 2 (axis j)))-
  (ContinuousLinearMap.compL ℝ (SphereSobolev 0) (SphereSobolev 0) (SphereSobolev 0)
    (coarseSphereScalarMulL (sphereCoordinate j))).comp
      (closedTwoJetCoarseScalarMultiplierL.comp (closedCoefficientDirectionalDerivativeL 2 (axis i)))

lemma closedCoefficientAngular_compatible (i j : I) (Q : ClosedCoefficientJets 3) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (closedCoefficientAngularOneL i j Q u) =
      closedCoefficientAngularCoarseL i j Q (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  change sphereSobolevInclusionL 1 0 (by norm_num)
    (oneSphereCoordinateMulL i (closedTwoJetOneBoundaryScalarMultiplierL (closedCoefficientDirectionalDerivativeL 2 (axis j) Q) u)-
     oneSphereCoordinateMulL j (closedTwoJetOneBoundaryScalarMultiplierL (closedCoefficientDirectionalDerivativeL 2 (axis i) Q) u)) = _
  rw [map_sub,oneSphereCoordinateMulL_coarse,oneSphereCoordinateMulL_coarse,
    closedTwoJet_scalar_multiplier_compatible,closedTwoJet_scalar_multiplier_compatible]
  rfl

lemma closedCoefficientAngularCoarseL_on_smooth (i j : I) (Q : SmoothCoefficientJets 3) :
    closedCoefficientAngularCoarseL i j (smoothCoefficientClosureInclusionL 3 Q) =
      coarseSphereScalarMulL (smoothSphereValue
        (smoothRotationData i j (coefficientSmoothData (smoothMultiplierLowerJets Q)))) := by
  let qj := smoothSphereValue (coefficientSmoothData (smoothCoefficientDirectionalDerivative 2 (axis j) Q))
  let qi := smoothSphereValue (coefficientSmoothData (smoothCoefficientDirectionalDerivative 2 (axis i) Q))
  have hValue : sphereCoordinate i*qj-sphereCoordinate j*qi =
      smoothSphereValue (smoothRotationData i j (coefficientSmoothData (smoothMultiplierLowerJets Q))) := by
    apply ContinuousMap.ext
    intro w
    change w.val i*coefficientValue 2 (smoothCoefficientDirectionalDerivative 2 (axis j) Q) w.val-
      w.val j*coefficientValue 2 (smoothCoefficientDirectionalDerivative 2 (axis i) Q) w.val =
      fderiv ℝ (coefficientValue 2 (smoothMultiplierLowerJets Q)) w.val (rotationVector i j w.val)
    rw [coefficientValue_smoothCoefficientDirectionalDerivative,coefficientValue_smoothCoefficientDirectionalDerivative,
      coefficientValue_smoothMultiplierLowerJets]
    simp only [rotationVector,axis,map_sub,map_smul,smul_eq_mul]
  apply ContinuousLinearMap.ext
  intro u
  change coarseSphereScalarMulL (sphereCoordinate i)
      (closedTwoJetCoarseScalarMultiplierL (closedCoefficientDirectionalDerivativeL 2 (axis j)
        (smoothCoefficientClosureInclusionL 3 Q)) u)-
    coarseSphereScalarMulL (sphereCoordinate j)
      (closedTwoJetCoarseScalarMultiplierL (closedCoefficientDirectionalDerivativeL 2 (axis i)
        (smoothCoefficientClosureInclusionL 3 Q)) u) = _
  rw [closedCoefficientDirectionalDerivativeL_on_smooth,closedCoefficientDirectionalDerivativeL_on_smooth,
    closedTwoJetCoarseScalarMultiplierL_on_smooth,closedTwoJetCoarseScalarMultiplierL_on_smooth]
  calc
    _ = coarseSphereScalarMulL (sphereCoordinate i*qj) u-coarseSphereScalarMulL (sphereCoordinate j*qi) u :=
      congrArg₂ (fun a b : SphereSobolev 0 => a-b)
        (coarseSphereScalarMulL_mul_apply _ _ u).symm (coarseSphereScalarMulL_mul_apply _ _ u).symm
    _ = coarseScalarMultiplierMapL (sphereCoordinate i*qj-sphereCoordinate j*qi) u :=
      (congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => A u)
        (coarseScalarMultiplierMapL.map_sub _ _)).symm
    _ = _ := congrArg (fun q => coarseScalarMultiplierMapL q u) hValue

/-- The completed coefficient angular generator is the actual H1
    multiplier rotation product rule, obtained from smooth dense inputs. -/
lemma closedCoefficientMultiplier_rotation_product (i j : I) (Q : ClosedCoefficientJets 3)
    (u : SphereSobolev 1) :
    sphereSobolevRotationL 1 i j (closedOneBoundaryScalarMultiplierL Q u) =
      closedCoefficientAngularCoarseL i j Q (sphereSobolevInclusionL 1 0 (by norm_num) u)+
        closedThreeJetCoarseScalarMultiplierL Q (sphereSobolevRotationL 1 i j u) := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      sphereSobolevRotationL 1 i j (closedOneBoundaryScalarMultiplierL Q u) =
        closedCoefficientAngularCoarseL i j Q (sphereSobolevInclusionL 1 0 (by norm_num) u)+
          closedThreeJetCoarseScalarMultiplierL Q (sphereSobolevRotationL 1 i j u) := by
    rintro _ ⟨P,rfl⟩
    rw [closedOneBoundaryScalarMultiplierL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth,
      closedCoefficientAngularCoarseL_on_smooth]
    exact congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u)
      (orderOneMultiplier_rotation_product (coefficientSmoothData (smoothMultiplierLowerJets P))
        (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets P))
        (oneBoundaryCoefficientMulL_coarse (smoothMultiplierLowerJets P)) i j)
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

lemma closedThreeJetCoarseScalarMultiplierL_symmetric (Q : ClosedCoefficientJets 3)
    (u v : SphereSobolev 0) :
    ⟪closedThreeJetCoarseScalarMultiplierL Q u,v⟫_ℝ = ⟪u,closedThreeJetCoarseScalarMultiplierL Q v⟫_ℝ := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      ⟪closedThreeJetCoarseScalarMultiplierL Q u,v⟫_ℝ = ⟪u,closedThreeJetCoarseScalarMultiplierL Q v⟫_ℝ := by
    rintro _ ⟨P,rfl⟩
    rw [closedThreeJetCoarseScalarMultiplierL_on_smooth]
    exact coarseSphereScalarMulL_symmetric _ _ _
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

lemma closedCoefficientAngularCoarseL_symmetric (i j : I) (Q : ClosedCoefficientJets 3)
    (u v : SphereSobolev 0) :
    ⟪closedCoefficientAngularCoarseL i j Q u,v⟫_ℝ = ⟪u,closedCoefficientAngularCoarseL i j Q v⟫_ℝ := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      ⟪closedCoefficientAngularCoarseL i j Q u,v⟫_ℝ = ⟪u,closedCoefficientAngularCoarseL i j Q v⟫_ℝ := by
    rintro _ ⟨P,rfl⟩
    rw [closedCoefficientAngularCoarseL_on_smooth]
    exact coarseSphereScalarMulL_symmetric _ _ _
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

end ShrinkingSpheres
