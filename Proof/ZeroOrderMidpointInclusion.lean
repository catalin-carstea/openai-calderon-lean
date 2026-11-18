import Proof.ZeroOrderMidpointShift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
private lemma norm_unit_sandwich_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : G →L[ℝ] H) (T : F →L[ℝ] G) (B : E →L[ℝ] F)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A.comp (T.comp B)‖ ≤ ‖T‖ := by
  have hTB : ‖T.comp B‖ ≤ ‖T‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left hB (norm_nonneg _)).trans_eq (mul_one _))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hA hTB (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
variable (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hc : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH=
      KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
lemma norm_zeroOrderMidpointL_le : ‖zeroOrderMidpointL KN KH hc‖ ≤ max ‖KN‖ ‖KH‖ := by
  have hL : ‖negativeHalfShiftToHalf KN‖ ≤ ‖KN‖ := norm_unit_sandwich_le _ _ _
    (norm_sphereSobolevBesselOrderL_le _ _) (norm_sphereSobolevBesselOrderL_le _ _)
  have hH : ‖halfShiftToThreeHalf KH‖ ≤ ‖KH‖ := norm_unit_sandwich_le _ _ _
    (norm_sphereSobolevBesselOrderL_le _ _) (norm_sphereSobolevBesselOrderL_le _ _)
  exact (norm_unit_sandwich_le _ _ _ (norm_sphereSobolevBesselOrderL_le _ _)
    (norm_sphereSobolevBesselOrderL_le _ _)).trans
      ((norm_sphereSobolevSameOrderMidpointL_le _ _ _).trans (max_le_max hL hH))

lemma zeroOrderMidpointL_lower_inclusion :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (zeroOrderMidpointL KN KH hc)=
      KN.comp (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) := by
  let Mid := sphereSobolevSameOrderMidpointL (negativeHalfShiftToHalf KN) (halfShiftToThreeHalf KH)
    (shifted_zero_order_compatibility KN KH hc)
  have hOut := sphereSobolevBesselOrderL_inclusion_comp 1 (1/2:ℝ) 0 (-(1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hIn := sphereSobolevBesselOrderL_inclusion_comp 0 (-(1/2:ℝ)) 1 (1/2:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
  have hMid := sphereSobolevSameOrderMidpointL_lower_inclusion (negativeHalfShiftToHalf KN)
    (halfShiftToThreeHalf KH) (shifted_zero_order_compatibility KN KH hc)
  calc
    _ = ((sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (sphereSobolevBesselOrderL 1 0)).comp (Mid.comp (sphereSobolevBesselOrderL 0 1)) := rfl
    _ = ((sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))).comp (Mid.comp (sphereSobolevBesselOrderL 0 1)) :=
      congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T.comp (Mid.comp (sphereSobolevBesselOrderL 0 1))) hOut
    _ = (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp
        (((sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).comp Mid).comp (sphereSobolevBesselOrderL 0 1)) := rfl
    _ = (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp
        (((negativeHalfShiftToHalf KN).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))).comp (sphereSobolevBesselOrderL 0 1)) :=
      congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (1/2:ℝ) =>
        (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp (T.comp (sphereSobolevBesselOrderL 0 1))) hMid
    _ = (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp
        ((negativeHalfShiftToHalf KN).comp ((sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).comp (sphereSobolevBesselOrderL 0 1))) := rfl
    _ = (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp
        ((negativeHalfShiftToHalf KN).comp ((sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)))) :=
      congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev (1/2:ℝ) =>
        (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp ((negativeHalfShiftToHalf KN).comp T)) hIn
    _ = _ := rfl
end ShrinkingSpheres
