import Proof.ClosedCoefficientFixedProduct
import Proof.FixedGeneratorScalarCommutators
import Proof.CoordinateScalarSmoothJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

def closedCoordinateCoefficientProductL (Q : SmoothCoefficientJets 2) (j : I) :
    ClosedCoefficientJets 3 →L[ℝ] ClosedCoefficientJets 3 :=
  closedCoefficientFixedProductL 3 (coordinateScalarSmoothJet Q j)

lemma coordinateScalarClosedJet_coarse (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (j : I) :
    closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q j))=
      coordinateMultiplierSobolevL 0 j := by
  rw [closedThreeJetCoarseScalarMultiplierL_on_smooth]
  have hV : smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets (coordinateScalarSmoothJet Q j)))=sphereCoordinate j := by
    ext w
    change coefficientValue 2 (smoothMultiplierLowerJets (coordinateScalarSmoothJet Q j)) w.val=w.val j
    rw [coefficientValue_smoothMultiplierLowerJets]
    exact coordinateScalarSmoothJet_value Q hQ j w
  rw [hV,coordinateMultiplierSobolevL_zero]

lemma coordinateScalarClosedJet_half (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (j : I) :
    closedThreeJetHalfBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q j))=
      coordinateMultiplierSobolevL (1/2:ℝ) j := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_half_scalar_multiplier_coarse,coordinateMultiplierSobolevL_half_coarse,
    coordinateScalarClosedJet_coarse Q hQ,coordinateMultiplierSobolevL_zero]

lemma coordinateScalarClosedJet_higher (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (j : I) :
    closedThreeJetHigherScalarMultiplierL (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q j))=
      coordinateMultiplierSobolevL (3/2:ℝ) j := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_higher_scalar_multiplier_coarse,coordinateScalarClosedJet_coarse Q hQ]
  exact (sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics (3/2:ℝ) 0 (by norm_num) (axis j) u).symm

lemma closedCoordinateCoefficientProduct_half (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (j : I) (P : ClosedCoefficientJets 3) :
    closedThreeJetHalfBoundaryScalarMultiplierL (closedCoordinateCoefficientProductL Q j P)=
      (coordinateMultiplierSobolevL (1/2:ℝ) j).comp (closedThreeJetHalfBoundaryScalarMultiplierL P) := by
  rw [closedCoordinateCoefficientProductL,closedThreeJetHalfScalarMultiplier_fixed_product,
    coordinateScalarClosedJet_half Q hQ]

lemma closedCoordinateCoefficientProduct_higher (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (j : I) (P : ClosedCoefficientJets 3) :
    closedThreeJetHigherScalarMultiplierL (closedCoordinateCoefficientProductL Q j P)=
      (coordinateMultiplierSobolevL (3/2:ℝ) j).comp (closedThreeJetHigherScalarMultiplierL P) := by
  rw [closedCoordinateCoefficientProductL,closedThreeJetHigherScalarMultiplier_fixed_product,
    coordinateScalarClosedJet_higher Q hQ]

lemma closedCoordinateCoefficientProduct_one (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (j : I) (P : ClosedCoefficientJets 3) :
    closedOneBoundaryScalarMultiplierL (closedCoordinateCoefficientProductL Q j P)=
      (coordinateMultiplierSobolevL 1 j).comp (closedOneBoundaryScalarMultiplierL P) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,closedThreeJet_scalar_multiplier_compatible,
    coordinateMultiplierSobolevL_coarse]
  rw [closedCoordinateCoefficientProductL,closedThreeJetCoarseScalarMultiplier_fixed_product,
    coordinateScalarClosedJet_coarse Q hQ,coordinateMultiplierSobolevL_zero]
  rfl

def closedUnitCoefficient (Q : SmoothCoefficientJets 2) : ClosedCoefficientJets 3 :=
  smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q)

lemma closedUnitCoefficient_coarse (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    closedThreeJetCoarseScalarMultiplierL (closedUnitCoefficient Q)=ContinuousLinearMap.id ℝ (SphereSobolev 0) := by
  rw [closedUnitCoefficient,closedThreeJetCoarseScalarMultiplierL_on_smooth]
  have hh : ∀ w : UnitSphere,coefficientValue 2 (smoothMultiplierLowerJets (coefficientThirdJet Q)) w.val=1 := by
    intro w
    rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_coefficientThirdJet]
    have hw : ‖w.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using w.property
    exact (hQ w.val (by simpa only [Metric.mem_closedBall,dist_zero_right,hw] using (le_refl (1:ℝ)))).eq_of_nhds
  simpa only [one_smul] using coarseSphereScalarMulL_const _ 1 hh

lemma closedUnitCoefficient_one (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    closedOneBoundaryScalarMultiplierL (closedUnitCoefficient Q)=ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  rw [closedThreeJet_scalar_multiplier_compatible,closedUnitCoefficient_coarse Q hQ]
  rfl

lemma closedUnitCoefficient_half (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    closedThreeJetHalfBoundaryScalarMultiplierL (closedUnitCoefficient Q)=ContinuousLinearMap.id ℝ (SphereSobolev (1/2:ℝ)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_half_scalar_multiplier_coarse,closedUnitCoefficient_coarse Q hQ]
  rfl

lemma closedUnitCoefficient_higher (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    closedThreeJetHigherScalarMultiplierL (closedUnitCoefficient Q)=ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_higher_scalar_multiplier_coarse,closedUnitCoefficient_coarse Q hQ]
  rfl
end ShrinkingSpheres
