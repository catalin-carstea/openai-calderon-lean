import Proof.FirstRadialRotationDerivative
import Proof.CommonSupportOneBoundaryDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

/-- A first correction's genuine angular derivative has a uniform L2 bound. -/
theorem rotation_first_correction_derivative_bound (q : X →L[ℝ] ℝ) (i j : I) (P : ℝ)
    (hP : 0 ≤ P) (hq : ‖q‖ ≤ P) :
    ‖fderiv ℝ (fun t : ℝ => radialCorrectionCovectorL
      (q.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)) 0‖ ≤ 12*P := by
  have hCurve := hasDerivAt_rotated_covector_zero q i j
  have hB := radialCorrectionCovectorL.hasFDerivAt.comp_hasDerivAt (0:ℝ) hCurve
  change HasDerivAt (fun t : ℝ => radialCorrectionCovectorL
    (q.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap))
    (radialCorrectionCovectorL (rotationCovector q i j)) 0 at hB
  have hComp : rotationCovector q i j = q.comp (rotationVectorL i j) := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [rotationCovector,ContinuousLinearMap.comp_apply,rotationVectorL_apply,rotationVector,
      map_sub,map_smul,_root_.sub_apply,_root_.smul_apply,PiLp.proj_apply,smul_eq_mul,axis]
    ring
  have hRot : ‖rotationCovector q i j‖ ≤ P*2 := by
    rw [hComp]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hq (norm_rotationVectorL_le_two i j) (norm_nonneg _) hP)
  apply norm_fderiv_le_of_hasDerivAt _ _ _ _ hB (by positivity)
  exact (norm_radialCorrectionCovectorL_apply_le _).trans
    ((mul_le_mul_of_nonneg_left hRot (by norm_num)).trans_eq (by ring))

end ShrinkingSpheres
