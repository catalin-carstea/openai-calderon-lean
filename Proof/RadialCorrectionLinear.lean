import Proof.FirstRadialOrderZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.BoundedAngularShift

/-- The bounded first radial correction depends linearly on its normalized
    center covector. All harmonic operators in this map are fixed. -/
def radialCorrectionCovectorL : (X →L[ℝ] ℝ) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics;
  -∑ i : I,(ContinuousLinearMap.apply ℝ ℝ (axis i)).smulRight
    (Z.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (((normalizedDerivative sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i).comp
        (radialDriftMultiplier orthogonalSphereHarmonics denseSphereHarmonics)).comp
          Z.symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem radialCorrectionCovectorL_apply (ell : X →L[ℝ] ℝ) :
    radialCorrectionCovectorL ell = coarseFirstRadialVariationL 1 ell := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [radialCorrectionCovectorL,coarseFirstRadialVariationL,inv_one,one_smul,
    radialDriftTraceL,ContinuousLinearMap.comp_apply,_root_.neg_apply,_root_.sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.apply_apply,_root_.smul_apply,
    map_neg,map_sum,map_smul]

theorem coarseFirstRadialVariationL_normalized_covector (c : ℝ) (ell : X →L[ℝ] ℝ) :
    coarseFirstRadialVariationL c ell = radialCorrectionCovectorL (c⁻¹ • ell) := by
  rw [map_smul,radialCorrectionCovectorL_apply]
  simp only [coarseFirstRadialVariationL,inv_one,one_smul]

theorem norm_radialCorrectionCovectorL_le : ‖radialCorrectionCovectorL‖ ≤ 6 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro ell
  rw [radialCorrectionCovectorL_apply]
  simpa only [inv_one,abs_one,mul_one] using norm_coarseFirstRadialVariationL_le 1 ell

theorem norm_radialCorrectionCovectorL_apply_le (ell : X →L[ℝ] ℝ) :
    ‖radialCorrectionCovectorL ell‖ ≤ 6*‖ell‖ :=
  (radialCorrectionCovectorL.le_opNorm ell).trans
    (mul_le_mul_of_nonneg_right norm_radialCorrectionCovectorL_le (norm_nonneg _))

/-- Parameter differentiation of the canonical correction reduces to
    differentiation of the normalized covector, without differentiating a DN inverse. -/
theorem hasFDerivAt_radialCorrectionCovector {q : X → (X →L[ℝ] ℝ)}
    {q' : X →L[ℝ] (X →L[ℝ] ℝ)} {y : X} (hq : HasFDerivAt q q' y) :
    HasFDerivAt (fun x => radialCorrectionCovectorL (q x))
      (radialCorrectionCovectorL.comp q') y :=
  radialCorrectionCovectorL.hasFDerivAt.comp y hq

end ShrinkingSpheres
