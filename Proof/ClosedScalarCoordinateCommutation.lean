import Proof.ClosedCoefficientAngularGenerators
import Proof.CoordinateMultiplierSobolev
import Proof.ClosedBoundaryGradientAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarseSphereScalarMulL_commute (q r : C(UnitSphere,ℝ)) :
    (coarseSphereScalarMulL q).comp (coarseSphereScalarMulL r) =
      (coarseSphereScalarMulL r).comp (coarseSphereScalarMulL q) := by
  apply ContinuousLinearMap.ext
  intro u
  calc
    _ = coarseSphereScalarMulL (q*r) u := (coarseSphereScalarMulL_mul_apply q r u).symm
    _ = coarseSphereScalarMulL (r*q) u := by rw [mul_comm]
    _ = _ := coarseSphereScalarMulL_mul_apply r q u

lemma closedThreeJetCoarseScalarMultiplier_coordinate_commute (Q : ClosedCoefficientJets 3) (j : I) :
    (closedThreeJetCoarseScalarMultiplierL Q).comp (coordinateMultiplierSobolevL 0 j) =
      (coordinateMultiplierSobolevL 0 j).comp (closedThreeJetCoarseScalarMultiplierL Q) := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      (closedThreeJetCoarseScalarMultiplierL Q).comp (coordinateMultiplierSobolevL 0 j) =
        (coordinateMultiplierSobolevL 0 j).comp (closedThreeJetCoarseScalarMultiplierL Q) := by
    rintro _ ⟨P,rfl⟩
    rw [closedThreeJetCoarseScalarMultiplierL_on_smooth,coordinateMultiplierSobolevL_zero]
    exact coarseSphereScalarMulL_commute _ _
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

lemma closedOneBoundaryScalarMultiplier_coordinate_commute (Q : ClosedCoefficientJets 3) (j : I) :
    (closedOneBoundaryScalarMultiplierL Q).comp (coordinateMultiplierSobolevL 1 j) =
      (coordinateMultiplierSobolevL 1 j).comp (closedOneBoundaryScalarMultiplierL Q) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  have hI (v : SphereSobolev 1) : sphereSobolevInclusionL 1 0 (by norm_num)
      (coordinateMultiplierSobolevL 1 j v) = coordinateMultiplierSobolevL 0 j
        (sphereSobolevInclusionL 1 0 (by norm_num) v) :=
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      1 0 (by norm_num) (axis j) v
  change sphereSobolevInclusionL 1 0 (by norm_num)
      (closedOneBoundaryScalarMultiplierL Q (coordinateMultiplierSobolevL 1 j u)) =
    sphereSobolevInclusionL 1 0 (by norm_num)
      (coordinateMultiplierSobolevL 1 j (closedOneBoundaryScalarMultiplierL Q u))
  rw [closedThreeJet_scalar_multiplier_compatible,hI,hI,closedThreeJet_scalar_multiplier_compatible]
  exact congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    T (sphereSobolevInclusionL 1 0 (by norm_num) u)) (closedThreeJetCoarseScalarMultiplier_coordinate_commute Q j)

lemma coordinateMultiplier_one_commute (i j : I) :
    (coordinateMultiplierSobolevL 1 i).comp (coordinateMultiplierSobolevL 1 j) =
      (coordinateMultiplierSobolevL 1 j).comp (coordinateMultiplierSobolevL 1 i) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  have hI (k : I) (v : SphereSobolev 1) : sphereSobolevInclusionL 1 0 (by norm_num)
      (coordinateMultiplierSobolevL 1 k v) = coordinateMultiplierSobolevL 0 k
        (sphereSobolevInclusionL 1 0 (by norm_num) v) :=
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      1 0 (by norm_num) (axis k) v
  change sphereSobolevInclusionL 1 0 (by norm_num)
      (coordinateMultiplierSobolevL 1 i (coordinateMultiplierSobolevL 1 j u)) =
    sphereSobolevInclusionL 1 0 (by norm_num)
      (coordinateMultiplierSobolevL 1 j (coordinateMultiplierSobolevL 1 i u))
  have h0 : (coordinateMultiplierSobolevL 0 i).comp (coordinateMultiplierSobolevL 0 j) =
      (coordinateMultiplierSobolevL 0 j).comp (coordinateMultiplierSobolevL 0 i) := by
    rw [coordinateMultiplierSobolevL_zero,coordinateMultiplierSobolevL_zero]
    exact coarseSphereScalarMulL_commute (sphereCoordinate i) (sphereCoordinate j)
  calc
    _ = coordinateMultiplierSobolevL 0 i (sphereSobolevInclusionL 1 0 (by norm_num)
        (coordinateMultiplierSobolevL 1 j u)) := hI i _
    _ = coordinateMultiplierSobolevL 0 i (coordinateMultiplierSobolevL 0 j
        (sphereSobolevInclusionL 1 0 (by norm_num) u)) := congrArg (coordinateMultiplierSobolevL 0 i) (hI j u)
    _ = coordinateMultiplierSobolevL 0 j (coordinateMultiplierSobolevL 0 i
        (sphereSobolevInclusionL 1 0 (by norm_num) u)) := congrArg
          (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T (sphereSobolevInclusionL 1 0 (by norm_num) u)) h0
    _ = coordinateMultiplierSobolevL 0 j (sphereSobolevInclusionL 1 0 (by norm_num)
        (coordinateMultiplierSobolevL 1 i u)) := congrArg (coordinateMultiplierSobolevL 0 j) (hI i u).symm
    _ = _ := (hI j _).symm

end ShrinkingSpheres
