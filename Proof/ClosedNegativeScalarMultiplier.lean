import Proof.ClosedHalfScalarCompatibility
import Proof.ClosedCoefficientAngularGenerators
import Proof.Archive.NativeHarmonicHalfCoarseDualPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

def closedThreeJetNegativeScalarMultiplierL : ClosedCoefficientJets 3 →L[ℝ]
    (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) ≃ₗᵢ[ℝ]
    (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))).toContinuousLinearEquiv.toContinuousLinearMap.comp
      closedThreeJetHalfBoundaryScalarMultiplierL

lemma closedThreeJet_negative_scalar_multiplier_coarse (Q : ClosedCoefficientJets 3) (u : SphereSobolev 0) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (closedThreeJetCoarseScalarMultiplierL Q u) =
      closedThreeJetNegativeScalarMultiplierL Q (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u) := by
  apply ext_inner_left ℝ
  intro v
  change sphereSobolevDualPairing (1/2:ℝ) v
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (closedThreeJetCoarseScalarMultiplierL Q u)) =
    sphereSobolevDualPairing (1/2:ℝ) v
      ((closedThreeJetHalfBoundaryScalarMultiplierL Q).adjoint (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u))
  have hAdj : sphereSobolevDualPairing (1/2:ℝ) v
      ((closedThreeJetHalfBoundaryScalarMultiplierL Q).adjoint (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u)) =
      sphereSobolevDualPairing (1/2:ℝ) (closedThreeJetHalfBoundaryScalarMultiplierL Q v)
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u) := by
    change ⟪v,(closedThreeJetHalfBoundaryScalarMultiplierL Q).adjoint _⟫_ℝ =
      ⟪closedThreeJetHalfBoundaryScalarMultiplierL Q v,_⟫_ℝ
    exact ContinuousLinearMap.adjoint_inner_right _ _ _
  rw [hAdj]
  simp only [sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num),
    closedThreeJet_half_scalar_multiplier_coarse]
  exact (closedThreeJetCoarseScalarMultiplierL_symmetric Q _ _).symm

lemma norm_closedThreeJetNegativeScalarMultiplierL_le :
    ‖closedThreeJetNegativeScalarMultiplierL‖ ≤ boundaryHalfMultiplierBudget := by
  apply ContinuousLinearMap.opNorm_le_bound _ boundaryHalfMultiplierBudget_nonneg
  intro Q
  change ‖(closedThreeJetHalfBoundaryScalarMultiplierL Q).adjoint‖ ≤ _
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact ((closedThreeJetHalfBoundaryScalarMultiplierL).le_opNorm Q).trans
    (mul_le_mul_of_nonneg_right norm_closedThreeJetHalfBoundaryScalarMultiplierL_le (norm_nonneg _))
end ShrinkingSpheres
