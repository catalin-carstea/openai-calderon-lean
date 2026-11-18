import Proof.ClosedNegativeDegreeScalarCommutator
import Proof.LinearScalarCoefficient
import Proof.FirstRadialAdjointCorrectionIdentity
import Proof.BoundaryAffineCoefficient
import Proof.ClosedNegativeScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

lemma first_correction_closed_scalar_negative_graph (F0 F1 : SmoothCoefficientMatrix 2)
    (ell : X →L[ℝ] ℝ) (Q : SmoothCoefficientJets 3)
    (hQ : ∀ w : UnitSphere,coefficientValue 3 Q w.val=ell w.val)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (hF1 : ∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) z=ell z*(1:Mat) i j)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (((radialCorrectionCovectorL ell).adjoint-radialCorrectionCovectorL ell).comp
        (sphereSobolevInclusionL 1 0 (by norm_num))) =
      (-(closedNegativeDegreeScalarCommutatorL F0 ha0 (smoothCoefficientClosureInclusionL 3 Q))).comp
        (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  have hNormal (w : UnitSphere) : coefficientValue 2 (normalCoefficientJet F1) w.val=ell w.val := by
    rw [coefficientValue_normalCoefficientJet]
    apply boundaryNormalCoefficient_scalar_sphere F1 ell
    intro v
    ext i j
    exact hF1 v.val (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall v.property)) i j
  have hOne : closedOneBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q)=
      oneBoundaryCoefficientMulL (normalCoefficientJet F1) := by
    rw [closedOneBoundaryScalarMultiplierL_on_smooth]
    apply oneBoundaryCoefficientMulL_congr_sphere
    intro w
    rw [coefficientValue_smoothMultiplierLowerJets,hQ w,hNormal w]
  have hCoarse : closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q)=
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1))) := by
    rw [closedThreeJetCoarseScalarMultiplierL_on_smooth]
    apply congrArg coarseSphereScalarMulL
    apply ContinuousMap.ext
    intro w
    change coefficientValue 2 (smoothMultiplierLowerJets Q) w.val=coefficientValue 2 (normalCoefficientJet F1) w.val
    rw [coefficientValue_smoothMultiplierLowerJets,hQ w,hNormal w]
  have hFirst := first_radial_adjoint_correction_normalized F0 F1 ell hF0 hF1 ha1 hInv0
  have hGraph := degree_closed_scalar_negative_graph F0 ha0
    (fun z hz => hF0 z (unitBall_subset_closedBall_two hz)) hInv0
    (smoothCoefficientClosureInclusionL 3 Q)
  unfold CommutatorLift at hGraph
  rw [hOne,hCoarse] at hGraph
  apply ContinuousLinearMap.ext
  intro u
  have hF := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) hFirst
  have hG := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u) hGraph
  change (radialCorrectionCovectorL ell).adjoint (sphereSobolevInclusionL 1 0 (by norm_num) u)=
    radialCorrectionCovectorL ell (sphereSobolevInclusionL 1 0 (by norm_num) u)+
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1))) (sphereSobolevDegreeL u)-
        sphereSobolevDegreeL (oneBoundaryCoefficientMulL (normalCoefficientJet F1) u) at hF
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (((radialCorrectionCovectorL ell).adjoint-radialCorrectionCovectorL ell)
      (sphereSobolevInclusionL 1 0 (by norm_num) u))= _
  rw [_root_.sub_apply,hF]
  have hEq : radialCorrectionCovectorL ell (sphereSobolevInclusionL 1 0 (by norm_num) u)+
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1))) (sphereSobolevDegreeL u)-
        sphereSobolevDegreeL (oneBoundaryCoefficientMulL (normalCoefficientJet F1) u)-
          radialCorrectionCovectorL ell (sphereSobolevInclusionL 1 0 (by norm_num) u)=
      -(sphereSobolevDegreeL (oneBoundaryCoefficientMulL (normalCoefficientJet F1) u)-
        coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1))) (sphereSobolevDegreeL u)) := by abel
  rw [hEq,map_neg]
  exact congrArg Neg.neg hG
end ShrinkingSpheres
