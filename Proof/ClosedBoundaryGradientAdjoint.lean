import Proof.VectorGradientAdjointJets
import Proof.ClosedOneBoundaryScalarMultiplier
import Proof.BoundaryGradientRealization
import Proof.FiniteJetBudgetAlgebra
import Proof.RadialTaylorHigherJets
import Proof.Archive.SphereContinuousScalarMultiplierProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarseSphereScalarMulL_mul_apply (q p : C(UnitSphere,ℝ)) (u : SphereSobolev 0) :
    coarseSphereScalarMulL (q*p) u = coarseSphereScalarMulL q (coarseSphereScalarMulL p u) := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  change Z (sphereContinuousScalarMulL (q*p) (Z.symm u)) =
    Z (sphereContinuousScalarMulL q (Z.symm (Z (sphereContinuousScalarMulL p (Z.symm u)))))
  rw [Z.symm_apply_apply,sphereContinuousScalarMulL_mul_apply]

/-- The normal multiplier is the same sum of coordinate multipliers on H1. -/
theorem oneBoundary_vectorNormal_decomposition (F : I → SmoothCoefficientJets 2) :
    oneBoundaryCoefficientMulL (vectorNormalJet F) =
      ∑ j : I,(oneSphereCoordinateMulL j).comp (oneBoundaryCoefficientMulL (F j)) := by
  have hSphere : smoothSphereValue (coefficientSmoothData (vectorNormalJet F)) =
      ∑ j : I,sphereCoordinate j*smoothSphereValue (coefficientSmoothData (F j)) := by
    apply ContinuousMap.ext
    intro w
    simp only [ContinuousMap.sum_apply,ContinuousMap.mul_apply]
    change coefficientValue 2 (vectorNormalJet F) w.val = ∑ j : I,w.val j*coefficientValue 2 (F j) w.val
    rw [coefficientValue_vectorNormalJet]
    rfl
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  rw [oneBoundaryCoefficientMulL_coarse]
  simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum,
    oneSphereCoordinateMulL_coarse,oneBoundaryCoefficientMulL_coarse]
  rw [hSphere]
  change coarseScalarMultiplierMapL (∑ j : I,sphereCoordinate j*smoothSphereValue (coefficientSmoothData (F j)))
      (sphereSobolevInclusionL 1 0 (by norm_num) u) = _
  rw [map_sum]
  simp only [_root_.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => coarseSphereScalarMulL_mul_apply _ _ _)

def closedVectorNormalMultiplier (Q : I → ClosedCoefficientJets 3) : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  ∑ j : I,(oneSphereCoordinateMulL j).comp (closedOneBoundaryScalarMultiplierL (Q j))

def closedVectorTangentialAdjoint (Q : I → ClosedCoefficientJets 3) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ j : I,∑ i : I,-(sphereSobolevRotationL 1 i j).comp
    ((oneSphereCoordinateMulL i).comp (closedOneBoundaryScalarMultiplierL (Q j)))

def closedBoundaryGradientAdjoint (Q : I → ClosedCoefficientJets 3)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  closedVectorTangentialAdjoint Q+Da.comp (closedVectorNormalMultiplier Q)

theorem closedBoundaryGradientAdjoint_on_smooth (Q : I → SmoothCoefficientJets 3)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    closedBoundaryGradientAdjoint (fun j => smoothCoefficientClosureInclusionL 3 (Q j)) Da =
      boundaryGradientAdjointL (fun j => smoothMultiplierLowerJets (Q j)) Da := by
  simp only [closedBoundaryGradientAdjoint,closedVectorTangentialAdjoint,closedVectorNormalMultiplier,
    closedOneBoundaryScalarMultiplierL_on_smooth,boundaryGradientAdjointL,adjointBoundaryTangentialL,
    oneBoundary_vectorNormal_decomposition]

lemma contDiffAt_closedBoundaryGradientAdjoint
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Q : I → P → ClosedCoefficientJets 3) (Da : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (p : P) (hQ : ∀ j,ContDiffAt ℝ ∞ (Q j) p) (hDa : ContDiffAt ℝ ∞ Da p) :
    ContDiffAt ℝ ∞ (fun t => closedBoundaryGradientAdjoint (fun j => Q j t) (Da t)) p := by
  simpa only [closedBoundaryGradientAdjoint,closedVectorTangentialAdjoint,closedVectorNormalMultiplier,
    vectorGradientAdjointOperator,vectorTangentialOperator,vectorNormalOperator] using
      contDiffAt_vectorGradientAdjointOperator closedOneBoundaryScalarMultiplierL oneSphereCoordinateMulL
        (sphereSobolevRotationL 1) Q Da p hQ hDa

def oneSphereCoordinateMultiplierBudget : ℝ := ∑ j : I,‖oneSphereCoordinateMulL j‖

/-- Quantitative finite jets for the actual boundary-gradient adjoint in its
    completed coefficient inputs. A small multiplier budget remains a factor. -/
theorem norm_iteratedFDeriv_closedBoundaryGradientAdjoint_le
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Q : I → P → ClosedCoefficientJets 3) (Da : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (p : P) (hQ : ∀ j,ContDiffAt ℝ ∞ (Q j) p) (hDa : ContDiffAt ℝ ∞ Da p)
    (N : ℕ) (BQ CD : ℝ) (hBQ : 0 ≤ BQ) (hCD : 0 ≤ CD)
    (hQJets : ∀ j : I,∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (Q j) p‖ ≤ BQ)
    (hDaJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n Da p‖ ≤ CD)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun t => closedBoundaryGradientAdjoint (fun j => Q j t) (Da t)) p‖ ≤
      (73*boundaryTangentialAdjointBudget+2^N*CD*(73*oneSphereCoordinateMultiplierBudget))*BQ := by
  simpa only [closedBoundaryGradientAdjoint,closedVectorTangentialAdjoint,closedVectorNormalMultiplier,
    vectorGradientAdjointOperator,vectorTangentialOperator,vectorNormalOperator,
    vectorTangentialOperatorBudget,vectorNormalOperatorBudget,boundaryTangentialAdjointBudget,
    oneSphereCoordinateMultiplierBudget] using
      norm_iteratedFDeriv_vectorGradientAdjointOperator_le closedOneBoundaryScalarMultiplierL oneSphereCoordinateMulL
        (sphereSobolevRotationL 1) 73 (by norm_num) norm_closedOneBoundaryScalarMultiplierL_le
        Q Da p hQ hDa N BQ CD hBQ hCD hQJets hDaJets n hn

end ShrinkingSpheres
