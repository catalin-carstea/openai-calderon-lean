import Proof.ClosedCoefficientAngularGenerators
import Proof.ClosedDegreeScalarCommutator
import Proof.BalancedHigherScalarCommutator
import Proof.CoordinateMultiplierSobolev
import Proof.ShiftedDegreeInclusion
import Proof.Archive.SphereSobolevConormalRotationDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

def closedCoefficientAngularHalfL (i j : I) : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) (SphereSobolev (1/2:ℝ))
    (SphereSobolev (1/2:ℝ)) (coordinateMultiplierSobolevL (1/2:ℝ) i)).comp
    (closedTwoJetHalfBoundaryScalarMultiplierL.comp (closedCoefficientDirectionalDerivativeL 2 (axis j)))-
  (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) (SphereSobolev (1/2:ℝ))
    (SphereSobolev (1/2:ℝ)) (coordinateMultiplierSobolevL (1/2:ℝ) j)).comp
    (closedTwoJetHalfBoundaryScalarMultiplierL.comp (closedCoefficientDirectionalDerivativeL 2 (axis i)))

lemma coordinateMultiplierSobolevL_half_coarse (i : I) (u : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (coordinateMultiplierSobolevL (1/2:ℝ) i u)=
      coarseSphereScalarMulL (sphereCoordinate i) (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u) := by
  have hh := sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics (1/2:ℝ) 0 (by norm_num) (axis i) u
  exact hh.trans (congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    A (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u)) (coordinateMultiplierSobolevL_zero i))

lemma closedCoefficientAngularHalfL_coarse (i j : I) (Q : ClosedCoefficientJets 3)
    (u : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (closedCoefficientAngularHalfL i j Q u)=
      closedCoefficientAngularCoarseL i j Q (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u) := by
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (coordinateMultiplierSobolevL (1/2:ℝ) i
      (closedTwoJetHalfBoundaryScalarMultiplierL (closedCoefficientDirectionalDerivativeL 2 (axis j) Q) u)-
    coordinateMultiplierSobolevL (1/2:ℝ) j
      (closedTwoJetHalfBoundaryScalarMultiplierL (closedCoefficientDirectionalDerivativeL 2 (axis i) Q) u))=_
  rw [map_sub,coordinateMultiplierSobolevL_half_coarse,coordinateMultiplierSobolevL_half_coarse,
    closedTwoJet_half_scalar_multiplier_coarse,closedTwoJet_half_scalar_multiplier_coarse]
  rfl

lemma rotation_closed_scalar_commutator_half_graph (i j : I) (Q : ClosedCoefficientJets 3) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((closedCoefficientAngularHalfL i j Q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=
    (sphereSobolevRotationL 1 i j).comp (closedOneBoundaryScalarMultiplierL Q)-
      (closedThreeJetCoarseScalarMultiplierL Q).comp (sphereSobolevRotationL 1 i j) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,closedCoefficientAngularHalfL_coarse]
  rw [sphereSobolevInclusionL_trans_apply,closedCoefficientMultiplier_rotation_product]
  abel

lemma sphereSobolevRotationL_threehalf_coarse (i j : I) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (sphereSobolevRotationL (3/2:ℝ) i j)=
      (sphereSobolevRotationL 1 i j).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hh := sphereSobolevRotationL_inclusion (3/2:ℝ) 1 (by norm_num) i j
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact DFunLike.congr_fun hh u |>.symm

lemma rotation_closed_scalar_commutator_higher_graph (i j : I) (Q : ClosedCoefficientJets 3) :
    (sphereSobolevRotationL (3/2:ℝ) i j).comp (closedThreeJetHigherScalarMultiplierL Q)-
      (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp (sphereSobolevRotationL (3/2:ℝ) i j)=
    (closedCoefficientAngularHalfL i j Q).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  balanced_higher_scalar_commutator _ _ _ Q (sphereSobolevRotationL_threehalf_coarse i j)
    (rotation_closed_scalar_commutator_half_graph i j Q)

lemma sphereSobolevShiftedDegreeL_threehalf_coarse :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))=
      sphereSobolevDegreeL.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hh := sphereSobolevShiftedDegreeL_inclusion (3/2:ℝ) 1 (by norm_num) u
  rw [sphereSobolevShiftedDegreeL_one_eq_degree] at hh
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact hh

lemma degree_closed_scalar_commutator_higher_graph (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible) (Q : ClosedCoefficientJets 3) :
    (sphereSobolevShiftedDegreeL (3/2:ℝ)).comp (closedThreeJetHigherScalarMultiplierL Q)-
      (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))=
    (closedHalfRadialScalarCommutatorL F0 ha0 Q).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  balanced_higher_scalar_commutator _ _ _ Q sphereSobolevShiftedDegreeL_threehalf_coarse
    (degree_closed_scalar_commutator_half_graph F0 ha0 hFlat hInv0 Q)
end ShrinkingSpheres
