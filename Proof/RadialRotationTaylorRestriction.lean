import Proof.FirstRadialOrderZero
import Proof.ActualMidpointRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

attribute [local irreducible] coarseFirstRadialVariationL highFirstRadialVariationL

/-- A genuine midpoint radial family and any ball-equivalent high
    representatives give the same Taylor remainder on high boundary data. -/
theorem midpoint_radial_taylor_high_restriction
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G F F0 F1 : SmoothCoefficientMatrix 2) (c r : ℝ) (hc : c ≠ 0)
    (q : X →L[ℝ] ℝ)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL G))
    (hGF : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 G z = coefficientMatrixField 2 F z)
    (hF0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hF1 : ∀ z ∈ (ballOpens:Set X),∀ i j,coefficientValue 2 (F1 i j) z = q z*(1:Mat) i j)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible) :
    (R-r • (coarseFirstRadialVariationL c q).comp (sphereSobolevInclusionL 1 0 (by norm_num))).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 c) := by
  have hP := strongPoissonL_congr_on_ball G F hGF
  have hHigh : actualHighRadialErrorL G = actualHighRadialErrorL F := by
    change fixedHalfOutwardTraceL.comp (strongPoissonL G)-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL =
      fixedHalfOutwardTraceL.comp (strongPoissonL F)-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL
    exact congrArg (fun Q => fixedHalfOutwardTraceL.comp Q-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL) hP
  have hFirst := highFirstRadialVariation_coarse_eq F0 F1 c hc q hF0 hF1 hInv0
  have hResidual : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 c) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)-
        r • (coarseFirstRadialVariationL c q).comp (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)) := by
    rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
    exact congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 =>
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)-r • T) hFirst
  have hB : ((coarseFirstRadialVariationL c q).comp (sphereSobolevInclusionL 1 0 (by norm_num))).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (coarseFirstRadialVariationL c q).comp (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (coarseFirstRadialVariationL c q)
      (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T f)
        (sphereSobolevInclusionL_trans (3/2:ℝ) 1 0 (by norm_num) (by norm_num)))
  rw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp,hR,hHigh]
  exact (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 =>
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)-r • T) hB).trans hResidual.symm

end ShrinkingSpheres
