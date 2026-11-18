import Proof.ClosedNegativeDegreeScalarCommutator
import Proof.ClosedNegativeScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

lemma closed_scalar_identity_of_one (Q : ClosedCoefficientJets 3)
    (hOne : closedOneBoundaryScalarMultiplierL Q=ContinuousLinearMap.id ℝ (SphereSobolev 1)) :
    closedThreeJetCoarseScalarMultiplierL Q=ContinuousLinearMap.id ℝ (SphereSobolev 0) ∧
      closedThreeJetNegativeScalarMultiplierL Q=ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ))) := by
  have hCoarse : closedThreeJetCoarseScalarMultiplierL Q=ContinuousLinearMap.id ℝ (SphereSobolev 0) := by
    have hEq : (fun u => closedThreeJetCoarseScalarMultiplierL Q u)=(fun u : SphereSobolev 0 => u) :=
      (denseRange_sphereSobolevInclusionL 1 0 (by norm_num)).equalizer
        (closedThreeJetCoarseScalarMultiplierL Q).continuous continuous_id (by
          funext u
          have hh := closedThreeJet_scalar_multiplier_compatible Q u
          rw [hOne,ContinuousLinearMap.id_apply] at hh
          exact hh.symm)
    exact ContinuousLinearMap.ext (congrFun hEq)
  refine ⟨hCoarse,?_⟩
  have hEq : (fun u => closedThreeJetNegativeScalarMultiplierL Q u)=(fun u : SphereSobolev (-(1/2:ℝ)) => u) :=
    (denseRange_sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).equalizer
      (closedThreeJetNegativeScalarMultiplierL Q).continuous continuous_id (by
        funext u
        have hh := closedThreeJet_negative_scalar_multiplier_coarse Q u
        rw [hCoarse,ContinuousLinearMap.id_apply] at hh
        exact hh.symm)
  exact ContinuousLinearMap.ext (congrFun hEq)

lemma smooth_unit_closed_scalar_one (Q : SmoothCoefficientJets 3)
    (hQ : ∀ w : UnitSphere,coefficientValue 3 Q w.val=1) :
    closedOneBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q)=ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
  rw [closedOneBoundaryScalarMultiplierL_on_smooth]
  simpa only [one_smul] using oneBoundaryCoefficientMulL_const_sphere (smoothMultiplierLowerJets Q) 1
    (fun w => by rw [coefficientValue_smoothMultiplierLowerJets];exact hQ w)

lemma closedNegativeDegreeScalarCommutator_unit (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : ClosedCoefficientJets 3) (hOne : closedOneBoundaryScalarMultiplierL Q=ContinuousLinearMap.id ℝ (SphereSobolev 1)) :
    closedNegativeDegreeScalarCommutatorL F0 ha0 Q=0 := by
  have hCoarse := (closed_scalar_identity_of_one Q hOne).1
  have hGraph := degree_closed_scalar_negative_graph F0 ha0 hFlat hInv0 Q
  unfold CommutatorLift at hGraph
  rw [hOne,hCoarse,ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp,sub_self,
    ContinuousLinearMap.comp_zero] at hGraph
  have hEq : (fun u => closedNegativeDegreeScalarCommutatorL F0 ha0 Q u)=(fun _ : SphereSobolev (-(1/2:ℝ)) => 0) :=
    (denseRange_sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)).equalizer
      (closedNegativeDegreeScalarCommutatorL F0 ha0 Q).continuous continuous_const (by
        funext u
        have hh := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u) hGraph
        exact hh.symm)
  exact ContinuousLinearMap.ext (congrFun hEq)
end ShrinkingSpheres
