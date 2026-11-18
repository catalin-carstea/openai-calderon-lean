import Proof.RadialCorrectionSobolev
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma radialCorrectionHalf_coarse (q : X →L[ℝ] ℝ) (u : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (radialCorrectionSobolevL (1/2:ℝ) q u) = radialCorrectionCovectorL q
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u) := by
  rw [← radialCorrectionSobolevL_zero]
  exact sphereSobolevInclusionL_radialDrift sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (1/2:ℝ) 0 (by norm_num) (radialCorrectionVector q) u

def radialCorrectionHalfMapL : (X →L[ℝ] ℝ) →L[ℝ]
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  LinearMap.mkContinuous
    { toFun := radialCorrectionSobolevL (1/2:ℝ)
      map_add' := by
        intro q r
        apply ContinuousLinearMap.ext
        intro u
        apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
        simp only [_root_.add_apply,map_add,radialCorrectionHalf_coarse]
      map_smul' := by
        intro c q
        apply ContinuousLinearMap.ext
        intro u
        apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
        simp only [_root_.smul_apply,map_smul,radialCorrectionHalf_coarse,RingHom.id_apply] }
    (6*radialDriftSobolevBound (1/2:ℝ)) (by
      intro q
      have hB : 0 ≤ radialDriftSobolevBound (1/2:ℝ) := zero_le_one.trans (le_max_left _ _)
      have h := norm_sphereSobolevRadialDriftL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
        (1/2:ℝ) (radialCorrectionVector q)
      exact h.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (radialCorrectionVector_coordinate_sum_le q) (by norm_num : (0:ℝ) ≤ 2)) hB).trans_eq (by ring)))

lemma radialCorrectionHalfMapL_apply (q : X →L[ℝ] ℝ) : radialCorrectionHalfMapL q =
    radialCorrectionSobolevL (1/2:ℝ) q := rfl

def radialCorrectionNegativeAdjointMapL : (X →L[ℝ] ℝ) →L[ℝ]
    (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) ≃ₗᵢ[ℝ]
    (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))).toContinuousLinearEquiv.toContinuousLinearMap.comp
      radialCorrectionHalfMapL

lemma radialCorrectionNegativeAdjointMapL_apply (q : X →L[ℝ] ℝ) :
    radialCorrectionNegativeAdjointMapL q = radialCorrectionAdjointSobolevL (-(1/2:ℝ)) q := by
  change (radialCorrectionSobolevL (1/2:ℝ) q).adjoint = _
  unfold radialCorrectionAdjointSobolevL sphereSobolevRadialDriftAdjointL
  rw [neg_neg]
  rfl

lemma radialCorrectionNegativeAdjoint_coarse (q : X →L[ℝ] ℝ) (u : SphereSobolev 0) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) ((radialCorrectionCovectorL q).adjoint u) =
      radialCorrectionNegativeAdjointMapL q (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u) := by
  rw [radialCorrectionNegativeAdjointMapL_apply,← radialCorrectionAdjointSobolevL_zero]
  exact sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    0 (-(1/2:ℝ)) (by norm_num) (radialCorrectionVector q) u
end ShrinkingSpheres
