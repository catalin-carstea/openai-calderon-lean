import Proof.FirstErrorScalarCoefficients
import Proof.ClosedNegativeScalarMultiplier
import Proof.RadialCorrectionSobolev
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma closedThreeJet_half_negative_scalar_multiplier (Q : ClosedCoefficientJets 3)
    (u : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (closedThreeJetHalfBoundaryScalarMultiplierL Q u)=
    closedThreeJetNegativeScalarMultiplierL Q
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) u) := by
  have h0 := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
    (closedThreeJet_half_scalar_multiplier_coarse Q u)
  calc
    _ = sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (closedThreeJetCoarseScalarMultiplierL Q (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u)) := by
        simpa only [sphereSobolevInclusionL_trans_apply] using h0
    _ = closedThreeJetNegativeScalarMultiplierL Q
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u)) :=
      closedThreeJet_negative_scalar_multiplier_coarse Q _
    _ = _ := by rw [sphereSobolevInclusionL_trans_apply]

def radialScalarBoundedHalfL (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (radialCorrectionAdjointSobolevL (1/2:ℝ) ell).comp (closedThreeJetHalfBoundaryScalarMultiplierL Q)

def radialScalarBoundedNegativeL (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (radialCorrectionAdjointSobolevL (-(1/2:ℝ)) ell).comp (closedThreeJetNegativeScalarMultiplierL Q)

lemma radialScalarBounded_half_negative_compatible (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (radialScalarBoundedHalfL ell Q)=
    (radialScalarBoundedNegativeL ell Q).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    (radialCorrectionAdjointSobolevL (1/2:ℝ) ell (closedThreeJetHalfBoundaryScalarMultiplierL Q u))=_
  rw [show sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (radialCorrectionAdjointSobolevL (1/2:ℝ) ell (closedThreeJetHalfBoundaryScalarMultiplierL Q u))=
    radialCorrectionAdjointSobolevL (-(1/2:ℝ)) ell
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (closedThreeJetHalfBoundaryScalarMultiplierL Q u)) from
      sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
        (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (radialCorrectionVector ell) _]
  rw [closedThreeJet_half_negative_scalar_multiplier]
  rfl

lemma radialCorrectionAdjointHalf_coarse (ell : X →L[ℝ] ℝ) (v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (radialCorrectionAdjointSobolevL (1/2:ℝ) ell v)=
      (radialCorrectionCovectorL ell).adjoint (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) v) := by
  have hh := sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (1/2:ℝ) 0 (by norm_num) (radialCorrectionVector ell) v
  exact hh.trans (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    T (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) v)) (radialCorrectionAdjointSobolevL_zero ell))

lemma radialScalarBoundedHalf_coarse_compatible (ell : X →L[ℝ] ℝ) (Q : ClosedCoefficientJets 3)
    (u : SphereSobolev 1) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (radialScalarBoundedHalfL ell Q (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))=
    (radialCorrectionCovectorL ell).adjoint
      (sphereSobolevInclusionL 1 0 (by norm_num) (closedOneBoundaryScalarMultiplierL Q u)) := by
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (radialCorrectionAdjointSobolevL (1/2:ℝ) ell (closedThreeJetHalfBoundaryScalarMultiplierL Q
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)))=_
  rw [← closedThreeJet_scalar_multiplier_one_half,radialCorrectionAdjointHalf_coarse]
  exact congrArg (radialCorrectionCovectorL ell).adjoint
    (sphereSobolevInclusionL_trans_apply 1 (1/2:ℝ) 0 (by norm_num) (by norm_num)
      (closedOneBoundaryScalarMultiplierL Q u))
end ShrinkingSpheres
