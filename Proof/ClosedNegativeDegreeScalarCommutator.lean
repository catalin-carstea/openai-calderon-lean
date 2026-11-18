import Proof.ClosedDegreeScalarCommutator
import Proof.NegativeCommutatorComposition
import Proof.BasicRadialAngularPackets
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

def closedNegativeDegreeScalarCommutatorL (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    ClosedCoefficientJets 3 →L[ℝ] (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  -(realHalfOperatorAdjointL.comp (closedHalfRadialScalarCommutatorL F0 ha0))

lemma degree_closed_scalar_negative_graph (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible) (Q : ClosedCoefficientJets 3) :
    CommutatorLift (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))
      (closedOneBoundaryScalarMultiplierL Q) (closedThreeJetCoarseScalarMultiplierL Q)
      sphereSobolevDegreeL (closedNegativeDegreeScalarCommutatorL F0 ha0 Q) := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      CommutatorLift (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
        (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))
        (closedOneBoundaryScalarMultiplierL Q) (closedThreeJetCoarseScalarMultiplierL Q)
        sphereSobolevDegreeL (closedNegativeDegreeScalarCommutatorL F0 ha0 Q) := by
    rintro _ ⟨Q,rfl⟩
    unfold CommutatorLift
    rw [closedOneBoundaryScalarMultiplierL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth]
    simp only [closedNegativeDegreeScalarCommutatorL,_root_.neg_apply,ContinuousLinearMap.comp_apply,
      closedHalfRadialScalarCommutatorL_on_smooth]
    exact adjoint_multiplier_gain_graph sphereSobolevDegreeL sphereSobolevDegreeL
      (halfRadialMultiplierCommutatorL F0 ha0 Q) Q degreeCoarseAdjointPacket.pairing
      (degree_smooth_scalar_commutator_half_graph F0 ha0 hFlat hInv0 Q)
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q
end ShrinkingSpheres
