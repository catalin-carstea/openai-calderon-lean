import Proof.GradedScalarRotationJacobi
import Proof.ClosedFourJetAngularDerivative
import Proof.ZeroOrderRotationHighLift
import Proof.LowScalarGeneratorCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma degree_scalar_rotation_graph
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q QR : ClosedCoefficientJets 3) (i j : I)
    (hQR : closedThreeJetHalfBoundaryScalarMultiplierL QR=closedCoefficientAngularHalfL i j Q)
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (closedHalfRadialScalarCommutatorL F0 ha0 Q (sphereSobolevRotationL (3/2:ℝ) i j u)+
        closedHalfRadialScalarCommutatorL F0 ha0 QR
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=
    sphereSobolevRotationL (1/2:ℝ) i j
      (closedHalfRadialScalarCommutatorL F0 ha0 Q
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) := by
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hPair : I0.comp (sphereSobolevShiftedDegreeL (3/2:ℝ))=
      (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp I1 :=
    balanced_endpoint_pair_of_coarse _ _ _ (ContinuousLinearMap.ext sphereSobolevDegreeL_half)
      sphereSobolevShiftedDegreeL_threehalf_coarse
  have hC := degree_closed_scalar_commutator_higher_graph F0 ha0 hFlat hInv0 Q
  have hCrHigh := degree_closed_scalar_commutator_higher_graph F0 ha0 hFlat hInv0 QR
  have hClow := balanced_low_scalar_commutator _ _ _ Q hPair hC
  have hCr := balanced_low_scalar_commutator _ _ _ QR hPair hCrHigh
  have hRotPair : I0.comp (sphereSobolevRotationL (3/2:ℝ) i j)=
      (sphereSobolevRotationL (1/2:ℝ) i j).comp I1 :=
    balanced_endpoint_pair_of_coarse _ _ _
      (ContinuousLinearMap.ext (fun v => oneRotation_half_inclusion i j v))
      (sphereSobolevRotationL_threehalf_coarse i j)
  have hQhigh := rotation_closed_scalar_commutator_higher_graph i j Q
  rw [← hQR] at hQhigh
  have hQlow := balanced_low_scalar_commutator _ _ _ Q hRotPair hQhigh
  have hR : (sphereSobolevRotationL (1/2:ℝ) i j).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))-
      (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (sphereSobolevRotationL (3/2:ℝ) i j)=
      I0.comp (0 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) := by
    have hh := sphereSobolevShiftedDegreeL_rotation_commute (3/2:ℝ) i j
    have hD : sphereSobolevShiftedDegreeL ((3/2:ℝ)-1)=sphereSobolevShiftedDegreeL (1/2:ℝ) := by congr 1 <;> norm_num
    have hRot : sphereSobolevRotationL ((3/2:ℝ)-1) i j=sphereSobolevRotationL (1/2:ℝ) i j := by congr 1 <;> norm_num
    rw [hD,hRot] at hh
    simpa only [ContinuousLinearMap.comp_zero] using sub_eq_zero.mpr hh.symm
  have hh := graded_scalar_rotation_jacobi I1 I0 (sphereSobolevShiftedDegreeL (3/2:ℝ))
    0 (sphereSobolevRotationL (3/2:ℝ) i j) (sphereSobolevShiftedDegreeL (1/2:ℝ))
    (sphereSobolevRotationL (1/2:ℝ) i j)
    (closedThreeJetHigherScalarMultiplierL Q) (closedThreeJetHalfBoundaryScalarMultiplierL Q)
    (closedThreeJetHalfBoundaryScalarMultiplierL QR) (closedHalfRadialScalarCommutatorL F0 ha0 Q)
    0 (closedHalfRadialScalarCommutatorL F0 ha0 QR)
    (closedThreeJetNegativeScalarMultiplierL Q) (closedThreeJetNegativeScalarMultiplierL QR)
    hPair (ContinuousLinearMap.ext (fun v => (closedThreeJet_half_negative_scalar_multiplier Q v).symm))
    (ContinuousLinearMap.ext (fun v => (closedThreeJet_half_negative_scalar_multiplier QR v).symm))
    hC hClow hR hQhigh hQlow (by simp only [ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,sub_self]) hCr u
  simpa only [zero_add] using hh

/-- Order-zero higher degree/scalar commutator from explicit angular data. -/
def closedHigherDegreeScalarFromRotationData (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : ClosedCoefficientJets 3) (R : I × I → ClosedCoefficientJets 3) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  zeroOrderRotationHighLiftL (closedHalfRadialScalarCommutatorL F0 ha0 Q)
    (fun i j => closedHalfRadialScalarCommutatorL F0 ha0 (R (i,j)))

lemma closedHigherDegreeScalarFromRotationData_compatible (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : ClosedCoefficientJets 3) (R : I × I → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j))=closedCoefficientAngularHalfL i j Q) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (closedHigherDegreeScalarFromRotationData F0 ha0 Q R)=
    (closedHalfRadialScalarCommutatorL F0 ha0 Q).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  zeroOrderRotationHighLiftL_compatible _ _ (fun u i j =>
    degree_scalar_rotation_graph F0 ha0 hFlat hInv0 Q (R (i,j)) i j (hR i j) u)

def closedHigherDegreeScalarCommutator (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (Q : ClosedCoefficientJets 4) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  closedHigherDegreeScalarFromRotationData F0 ha0 (closedCoefficientLowerJetsL 3 Q)
    (fun ij => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 Q)

lemma closedHigherDegreeScalarCommutator_compatible (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (Q : ClosedCoefficientJets 4) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (closedHigherDegreeScalarCommutator F0 ha0 Q0 Q)=
    (closedHalfRadialScalarCommutatorL F0 ha0 (closedCoefficientLowerJetsL 3 Q)).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  closedHigherDegreeScalarFromRotationData_compatible F0 ha0 hFlat hInv0
    (closedCoefficientLowerJetsL 3 Q) (fun ij => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 Q)
    (fun i j => closedFourJetAngularDerivative_half Q0 hQ0 i j Q)
end ShrinkingSpheres
