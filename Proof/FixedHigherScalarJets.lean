import Proof.FixedDegreeHigherScalarCommutator
import Proof.NativeScalarHigherJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma closedHigherDegreeScalarFromRotationData_graph (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : ClosedCoefficientJets 3) (R : I × I → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j))=closedCoefficientAngularHalfL i j Q) :
    (sphereSobolevShiftedDegreeL (3/2:ℝ)).comp (closedThreeJetHigherScalarMultiplierL Q)-
      (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))=
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (closedHigherDegreeScalarFromRotationData F0 ha0 Q R) :=
  (degree_closed_scalar_commutator_higher_graph F0 ha0 hFlat hInv0 Q).trans
    (closedHigherDegreeScalarFromRotationData_compatible F0 ha0 hFlat hInv0 Q R hR).symm

lemma closedHigherDegreeScalarFromRotationData_jets
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : P → ClosedCoefficientJets 3) (R : I × I → P → ClosedCoefficientJets 3)
    (p : P) (N : ℕ) (BQ BR : ℝ) (hQ : SmoothFiniteJetBound Q p N BQ)
    (hR : ∀ ij,SmoothFiniteJetBound (R ij) p N BR) :
    SmoothFiniteJetBound (fun x => closedHigherDegreeScalarFromRotationData F0 ha0 (Q x) (fun ij => R ij x)) p N
      ((19+9*Real.sqrt 2)*‖closedHalfRadialScalarCommutatorL F0 ha0‖*(BQ+BR)) := by
  let CD := ‖closedHalfRadialScalarCommutatorL F0 ha0‖
  let B := CD*(BQ+BR)
  have hCD : 0 ≤ CD := norm_nonneg _
  have hBR : 0 ≤ BR := (hR (0,0)).nonneg
  have hLow := (hQ.clm (closedHalfRadialScalarCommutatorL F0 ha0)).weaken
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBR) hCD)
  have hG (ij : I × I) : SmoothFiniteJetBound
      (fun x => closedHalfRadialScalarCommutatorL F0 ha0 (R ij x)) p N B :=
    ((hR ij).clm (closedHalfRadialScalarCommutatorL F0 ha0)).weaken
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hQ.nonneg) hCD)
  have hh := smoothFiniteJetBound_zero_order_rotation_high_lift _ _ p N B hLow hG
  exact hh.weaken (le_of_eq (by dsimp only [B,CD];ring))

lemma closedHigherDegreeScalarCommutator_graph (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (Q : ClosedCoefficientJets 4) :
    (sphereSobolevShiftedDegreeL (3/2:ℝ)).comp
        (closedThreeJetHigherScalarMultiplierL (closedCoefficientLowerJetsL 3 Q))-
      (closedThreeJetHalfBoundaryScalarMultiplierL (closedCoefficientLowerJetsL 3 Q)).comp
        (sphereSobolevShiftedDegreeL (3/2:ℝ))=
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (closedHigherDegreeScalarCommutator F0 ha0 Q0 Q) :=
  (degree_closed_scalar_commutator_higher_graph F0 ha0 hFlat hInv0 (closedCoefficientLowerJetsL 3 Q)).trans
    (closedHigherDegreeScalarCommutator_compatible F0 ha0 hFlat hInv0 Q0 hQ0 Q).symm

lemma closedHigherDegreeScalarCommutator_jets
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (Q : P → ClosedCoefficientJets 4)
    (p : P) (N : ℕ) (BQ : ℝ) (hQ : SmoothFiniteJetBound Q p N BQ) :
    SmoothFiniteJetBound (fun x => closedHigherDegreeScalarCommutator F0 ha0 Q0 (Q x)) p N
      (((19+9*Real.sqrt 2)*‖closedHalfRadialScalarCommutatorL F0 ha0‖*
        (1+scalarAngularCoefficientBudget Q0))*BQ) := by
  have hLower := (hQ.clm (closedCoefficientLowerJetsL 3)).weaken
    ((mul_le_mul_of_nonneg_right (norm_closedCoefficientLowerJetsL_le 3) hQ.nonneg).trans_eq (one_mul _))
  have hR (ij : I × I) : SmoothFiniteJetBound
      (fun x => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 (Q x)) p N
      (scalarAngularCoefficientBudget Q0*BQ) :=
    (hQ.clm (closedFourJetAngularDerivativeL Q0 ij.1 ij.2)).weaken
      (mul_le_mul_of_nonneg_right ((scalarAngularCoefficientBudget_bounds Q0).2 ij.1 ij.2) hQ.nonneg)
  have hh := closedHigherDegreeScalarFromRotationData_jets F0 ha0 _ _ p N
    BQ (scalarAngularCoefficientBudget Q0*BQ) hLower hR
  exact hh.weaken (le_of_eq (by ring))

def closedHigherRotationScalarCommutator (Q0 : SmoothCoefficientJets 2) (i j : I)
    (Q : ClosedCoefficientJets 4) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  closedThreeJetHigherScalarMultiplierL (closedFourJetAngularDerivativeL Q0 i j Q)

lemma closedHigherRotationScalarCommutator_compatible (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (i j : I) (Q : ClosedCoefficientJets 4) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (closedHigherRotationScalarCommutator Q0 i j Q)=
    (closedCoefficientAngularHalfL i j (closedCoefficientLowerJetsL 3 Q)).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.comp_apply,closedHigherRotationScalarCommutator,
    closedThreeJet_higher_scalar_multiplier_half,closedFourJetAngularDerivative_half Q0 hQ0]
  rfl

lemma closedHigherRotationScalarCommutator_graph (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (i j : I) (Q : ClosedCoefficientJets 4) :
    (sphereSobolevRotationL (3/2:ℝ) i j).comp
        (closedThreeJetHigherScalarMultiplierL (closedCoefficientLowerJetsL 3 Q))-
      (closedThreeJetHalfBoundaryScalarMultiplierL (closedCoefficientLowerJetsL 3 Q)).comp
        (sphereSobolevRotationL (3/2:ℝ) i j)=
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (closedHigherRotationScalarCommutator Q0 i j Q) :=
  (rotation_closed_scalar_commutator_higher_graph i j (closedCoefficientLowerJetsL 3 Q)).trans
    (closedHigherRotationScalarCommutator_compatible Q0 hQ0 i j Q).symm

lemma closedHigherRotationScalarCommutator_jets
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Q0 : SmoothCoefficientJets 2) (i j : I) (Q : P → ClosedCoefficientJets 4)
    (p : P) (N : ℕ) (BQ : ℝ) (hQ : SmoothFiniteJetBound Q p N BQ) :
    SmoothFiniteJetBound (fun x => closedHigherRotationScalarCommutator Q0 i j (Q x)) p N
      ((‖closedThreeJetHigherScalarMultiplierL‖*scalarAngularCoefficientBudget Q0)*BQ) := by
  have hA := (hQ.clm (closedFourJetAngularDerivativeL Q0 i j)).weaken
    (mul_le_mul_of_nonneg_right ((scalarAngularCoefficientBudget_bounds Q0).2 i j) hQ.nonneg)
  exact (hA.clm closedThreeJetHigherScalarMultiplierL).weaken (le_of_eq (by ring))
end ShrinkingSpheres
