import Proof.RadialScalarBoundedEndpoints
import Proof.ClosedHigherScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def radialScalarBoundedHigherL (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (radialCorrectionAdjointSobolevL (3/2:ℝ) ell).comp (closedThreeJetHigherScalarMultiplierL Q)

def radialScalarBoundedAdjointHigherL (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (closedThreeJetHigherScalarMultiplierL Q).comp (radialCorrectionSobolevL (3/2:ℝ) ell)

lemma radialScalarBoundedHigherL_compatible (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (radialScalarBoundedHigherL ell Q)=
      (radialScalarBoundedHalfL ell Q).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    (radialCorrectionAdjointSobolevL (3/2:ℝ) ell (closedThreeJetHigherScalarMultiplierL Q u))=_
  have hh := sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (3/2:ℝ) (1/2:ℝ) (by norm_num) (radialCorrectionVector ell) (closedThreeJetHigherScalarMultiplierL Q u)
  exact hh.trans (congrArg (radialCorrectionAdjointSobolevL (1/2:ℝ) ell)
    (closedThreeJet_higher_scalar_multiplier_half Q u))

lemma radialScalarBoundedNegativeL_adjoint (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    (radialScalarBoundedNegativeL ell Q).adjoint=
      (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp (radialCorrectionSobolevL (1/2:ℝ) ell) := by
  rw [radialScalarBoundedNegativeL,ContinuousLinearMap.adjoint_comp]
  have hM : (closedThreeJetNegativeScalarMultiplierL Q).adjoint=closedThreeJetHalfBoundaryScalarMultiplierL Q :=
    ContinuousLinearMap.adjoint_adjoint _
  have hR : (radialCorrectionAdjointSobolevL (-(1/2:ℝ)) ell).adjoint=radialCorrectionSobolevL (1/2:ℝ) ell := by
    change ((radialCorrectionSobolevL (-(-(1/2:ℝ))) ell).adjoint).adjoint=_
    rw [ContinuousLinearMap.adjoint_adjoint,neg_neg]
  rw [hM,hR]

lemma radialScalarBoundedAdjointHigherL_compatible (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (radialScalarBoundedAdjointHigherL ell Q)=
      (radialScalarBoundedNegativeL ell Q).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [radialScalarBoundedNegativeL_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    (closedThreeJetHigherScalarMultiplierL Q (radialCorrectionSobolevL (3/2:ℝ) ell u))=_
  rw [closedThreeJet_higher_scalar_multiplier_half]
  exact congrArg (closedThreeJetHalfBoundaryScalarMultiplierL Q)
    (sphereSobolevInclusionL_radialDrift sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      (3/2:ℝ) (1/2:ℝ) (by norm_num) (radialCorrectionVector ell) u)

lemma norm_radialScalarBoundedHigherL_le (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    ‖radialScalarBoundedHigherL ell Q‖ ≤
      (6*radialDriftSobolevBound (-(3/2:ℝ))*‖closedThreeJetHigherScalarMultiplierL‖)*‖ell‖*‖Q‖ := by
  have hB : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hRaw := norm_sphereSobolevRadialDriftAdjointL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (3/2:ℝ) (radialCorrectionVector ell)
  have hR : ‖radialCorrectionAdjointSobolevL (3/2:ℝ) ell‖ ≤ 6*‖ell‖*radialDriftSobolevBound (-(3/2:ℝ)) :=
    hRaw.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (radialCorrectionVector_coordinate_sum_le ell) (by norm_num : (0:ℝ) ≤ 2)) hB).trans_eq (by ring))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hR (closedThreeJetHigherScalarMultiplierL.le_opNorm Q) (norm_nonneg _) (by positivity)).trans_eq (by ring))

lemma norm_radialScalarBoundedAdjointHigherL_le (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    ‖radialScalarBoundedAdjointHigherL ell Q‖ ≤
      (6*radialDriftSobolevBound (3/2:ℝ)*‖closedThreeJetHigherScalarMultiplierL‖)*‖ell‖*‖Q‖ := by
  have hB : 0 ≤ radialDriftSobolevBound (3/2:ℝ) := zero_le_one.trans (le_max_left _ _)
  have hRaw := norm_sphereSobolevRadialDriftL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (3/2:ℝ) (radialCorrectionVector ell)
  have hR : ‖radialCorrectionSobolevL (3/2:ℝ) ell‖ ≤ 6*‖ell‖*radialDriftSobolevBound (3/2:ℝ) :=
    hRaw.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (radialCorrectionVector_coordinate_sum_le ell) (by norm_num : (0:ℝ) ≤ 2)) hB).trans_eq (by ring))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (closedThreeJetHigherScalarMultiplierL.le_opNorm Q) hR (norm_nonneg _) (by positivity)).trans_eq (by ring))
end ShrinkingSpheres
