import Proof.RadialScalarCoarseEndpoints
import Proof.ActualNormalScalarCoefficientBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def radialScalarEndpointBudget (CQ : ℝ) : ℝ :=
  1+|6*CQ*radialDriftSobolevBound (-(1/2:ℝ))*‖closedThreeJetHalfBoundaryScalarMultiplierL‖|+
    |6*CQ*radialDriftSobolevBound (1/2:ℝ)*‖closedThreeJetNegativeScalarMultiplierL‖|

lemma radialScalarEndpointBudget_pos (CQ : ℝ) : 0 < radialScalarEndpointBudget CQ := by
  unfold radialScalarEndpointBudget
  positivity

lemma norm_radialScalarBounded_endpoints_le (CQ : ℝ) (hCQ : 0 ≤ CQ)
    (ell : X →L[ℝ] ℝ) (hEll : ‖ell‖ ≤ CQ) (Q : ClosedCoefficientJets 3) (B : ℝ)
    (hB : 0 ≤ B) (hQ : ‖Q‖ ≤ B) :
    ‖radialScalarBoundedHalfL ell Q‖ ≤ radialScalarEndpointBudget CQ*B ∧
    ‖radialScalarBoundedNegativeL ell Q‖ ≤ radialScalarEndpointBudget CQ*B := by
  have hDrift (t : ℝ) : 0 ≤ radialDriftSobolevBound t :=
    zero_le_one.trans (le_max_left _ _)
  have hRadial (t : ℝ) : ‖radialCorrectionAdjointSobolevL t ell‖ ≤
      6*CQ*radialDriftSobolevBound (-t) := by
    have hh := norm_sphereSobolevRadialDriftAdjointL_le sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics t (radialCorrectionVector ell)
    have hC := (radialCorrectionVector_coordinate_sum_le ell).trans (mul_le_mul_of_nonneg_left hEll (by norm_num : (0:ℝ) ≤ 3))
    exact hh.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hC (by norm_num : (0:ℝ) ≤ 2)) (hDrift (-t))).trans_eq (by ring))
  have hHalf : 6*CQ*radialDriftSobolevBound (-(1/2:ℝ))*‖closedThreeJetHalfBoundaryScalarMultiplierL‖ ≤
      radialScalarEndpointBudget CQ := by
    unfold radialScalarEndpointBudget
    linarith [le_abs_self (6*CQ*radialDriftSobolevBound (-(1/2:ℝ))*‖closedThreeJetHalfBoundaryScalarMultiplierL‖),
      abs_nonneg (6*CQ*radialDriftSobolevBound (1/2:ℝ)*‖closedThreeJetNegativeScalarMultiplierL‖)]
  have hNeg : 6*CQ*radialDriftSobolevBound (1/2:ℝ)*‖closedThreeJetNegativeScalarMultiplierL‖ ≤
      radialScalarEndpointBudget CQ := by
    unfold radialScalarEndpointBudget
    linarith [le_abs_self (6*CQ*radialDriftSobolevBound (1/2:ℝ)*‖closedThreeJetNegativeScalarMultiplierL‖),
      abs_nonneg (6*CQ*radialDriftSobolevBound (-(1/2:ℝ))*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)]
  constructor
  · calc
      _ ≤ ‖radialCorrectionAdjointSobolevL (1/2:ℝ) ell‖*‖closedThreeJetHalfBoundaryScalarMultiplierL Q‖ :=
        (radialCorrectionAdjointSobolevL (1/2:ℝ) ell).opNorm_comp_le _
      _ ≤ (6*CQ*radialDriftSobolevBound (-(1/2:ℝ)))*(‖closedThreeJetHalfBoundaryScalarMultiplierL‖*B) :=
        mul_le_mul (hRadial (1/2:ℝ))
          ((closedThreeJetHalfBoundaryScalarMultiplierL.le_opNorm Q).trans
            (mul_le_mul_of_nonneg_left hQ (norm_nonneg _))) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hCQ) (hDrift _))
      _ = (6*CQ*radialDriftSobolevBound (-(1/2:ℝ))*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hHalf hB
  · have hR := hRadial (-(1/2:ℝ))
    rw [neg_neg] at hR
    calc
      _ ≤ ‖radialCorrectionAdjointSobolevL (-(1/2:ℝ)) ell‖*‖closedThreeJetNegativeScalarMultiplierL Q‖ :=
        (radialCorrectionAdjointSobolevL (-(1/2:ℝ)) ell).opNorm_comp_le _
      _ ≤ (6*CQ*radialDriftSobolevBound (1/2:ℝ))*(‖closedThreeJetNegativeScalarMultiplierL‖*B) :=
        mul_le_mul hR ((closedThreeJetNegativeScalarMultiplierL.le_opNorm Q).trans
            (mul_le_mul_of_nonneg_left hQ (norm_nonneg _))) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hCQ) (hDrift _))
      _ = (6*CQ*radialDriftSobolevBound (1/2:ℝ)*‖closedThreeJetNegativeScalarMultiplierL‖)*B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hNeg hB
end ShrinkingSpheres
