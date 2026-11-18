import Proof.VectorGradientAdjointJets
import Proof.ClosedHalfScalarCompatibility
import Proof.CoordinateMultiplierSobolev
import Proof.ClosedBoundaryGradientAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 1800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def halfBoundaryGradientAdjoint (Q : I → ClosedCoefficientJets 3)
    (Da : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  vectorGradientAdjointOperator closedThreeJetHalfBoundaryScalarMultiplierL
    (coordinateMultiplierSobolevL (1/2:ℝ)) (sphereSobolevRotationL (1/2:ℝ)) Q Da

lemma oneSphereCoordinateMulL_half (i : I) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (oneSphereCoordinateMulL i u) =
      coordinateMultiplierSobolevL (1/2:ℝ) i (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) := by
  simpa only [oneSphereCoordinateMulL,coordinateMultiplierSobolevL,axis] using
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      1 (1/2:ℝ) (by norm_num) (axis i) u

lemma oneRotation_half_inclusion (i j : I) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevRotationL 1 i j u) =
      sphereSobolevRotationL (1/2:ℝ) i j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) := by
  have hh := sphereSobolevRotationL_inclusion_apply 1 (1/2:ℝ) (by norm_num) i j u
  have hI : (sphereSobolevInclusionL ((1:ℝ)-1) ((1/2:ℝ)-1) (by norm_num) :
      SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ))) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact hh.symm

lemma halfBoundaryGradientAdjoint_coarse_compatible
    (Q : I → ClosedCoefficientJets 3) (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Dah : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hDa : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp Da =
      Dah.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (closedBoundaryGradientAdjoint Q Da) =
      (halfBoundaryGradientAdjoint Q Dah).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hN : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (closedVectorNormalMultiplier Q u) =
      vectorNormalOperator closedThreeJetHalfBoundaryScalarMultiplierL (coordinateMultiplierSobolevL (1/2:ℝ)) Q
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) := by
    simp only [closedVectorNormalMultiplier,vectorNormalOperator,_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [oneSphereCoordinateMulL_half,closedThreeJet_scalar_multiplier_one_half]
  have hT : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (closedVectorTangentialAdjoint Q u) =
      vectorTangentialOperator closedThreeJetHalfBoundaryScalarMultiplierL (coordinateMultiplierSobolevL (1/2:ℝ))
        (sphereSobolevRotationL (1/2:ℝ)) Q (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) := by
    simp only [closedVectorTangentialAdjoint,vectorTangentialOperator,_root_.sum_apply,ContinuousLinearMap.comp_apply,
      _root_.neg_apply,map_sum,map_neg]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [oneRotation_half_inclusion,oneSphereCoordinateMulL_half,closedThreeJet_scalar_multiplier_one_half]
  have hD := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A (closedVectorNormalMultiplier Q u)) hDa
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (closedVectorTangentialAdjoint Q u+Da (closedVectorNormalMultiplier Q u)) = _
  simp only [ContinuousLinearMap.comp_apply] at hD
  rw [map_add,hT,hD,hN]
  rfl

lemma contDiffAt_halfBoundaryGradientAdjoint
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Q : I → P → ClosedCoefficientJets 3)
    (Da : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (p : P)
    (hQ : ∀ j,ContDiffAt ℝ ∞ (Q j) p) (hDa : ContDiffAt ℝ ∞ Da p) :
    ContDiffAt ℝ ∞ (fun x => halfBoundaryGradientAdjoint (fun j => Q j x) (Da x)) p :=
  contDiffAt_vectorGradientAdjointOperator _ _ _ Q Da p hQ hDa

def halfBoundaryGradientJetBudget (N : ℕ) (CD : ℝ) : ℝ :=
  boundaryHalfMultiplierBudget*vectorTangentialOperatorBudget (coordinateMultiplierSobolevL (1/2:ℝ))
    (sphereSobolevRotationL (1/2:ℝ))+
    2^N*CD*(boundaryHalfMultiplierBudget*vectorNormalOperatorBudget (coordinateMultiplierSobolevL (1/2:ℝ)))

lemma halfBoundaryGradientJetBudget_nonneg (N : ℕ) {CD : ℝ} (hCD : 0 ≤ CD) :
    0 ≤ halfBoundaryGradientJetBudget N CD := by
  have hHalf := boundaryHalfMultiplierBudget_nonneg
  unfold halfBoundaryGradientJetBudget vectorTangentialOperatorBudget vectorNormalOperatorBudget
  positivity

lemma norm_iteratedFDeriv_halfBoundaryGradientAdjoint_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Q : I → P → ClosedCoefficientJets 3)
    (Da : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (p : P)
    (hQ : ∀ j,ContDiffAt ℝ ∞ (Q j) p) (hDa : ContDiffAt ℝ ∞ Da p)
    (N : ℕ) (BQ CD : ℝ) (hBQ : 0 ≤ BQ) (hCD : 0 ≤ CD)
    (hQJets : ∀ j : I,∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (Q j) p‖ ≤ BQ)
    (hDaJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n Da p‖ ≤ CD)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun x => halfBoundaryGradientAdjoint (fun j => Q j x) (Da x)) p‖ ≤
      halfBoundaryGradientJetBudget N CD*BQ :=
  norm_iteratedFDeriv_vectorGradientAdjointOperator_le _ _ _ boundaryHalfMultiplierBudget
    boundaryHalfMultiplierBudget_nonneg norm_closedThreeJetHalfBoundaryScalarMultiplierL_le
    Q Da p hQ hDa N BQ CD hBQ hCD hQJets hDaJets n hn
end ShrinkingSpheres
