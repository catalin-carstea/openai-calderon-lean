import Proof.PhysicalCorrectionCoframeEndpoints
import Proof.FirstRadialAngularFieldJets
import Proof.ActualCoframeSobolevMultiplier
import Proof.FrameCoordinateCovectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma firstFrameCorrectionCoarseFamily_first_radial_form (d : Data) (j : I) (x : X) :
    firstFrameCorrectionCoarseFamily d j x =
      (firstRadialAdjointOperatorMapL (firstDensityLogCovector d x)).comp (coordinateMultiplierSobolevL 1 j)+
        scaledFrameLogRadius d.radius d.frame j x • firstRadialAdjointOperatorMapL (firstDensityLogCovector d x) := by
  apply ContinuousLinearMap.ext
  intro u
  have hMI : sphereSobolevInclusionL 1 0 (by norm_num) (coordinateMultiplierSobolevL 1 j u)=
      coordinateMultiplierSobolevL 0 j (sphereSobolevInclusionL 1 0 (by norm_num) u) :=
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics 1 0 (by norm_num) (axis j) u
  simp only [firstFrameCorrectionCoarseFamily,firstFrameAdjointCorrectionL,
    firstRadialAdjointOperatorMapL_apply,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.smul_apply,
    firstRadialCorrectionL_eq_covector,hMI]

lemma coframe_scaled_log_radius_sum (d : Data) (x b : X)
    (hFrame : ∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hr : DifferentiableAt ℝ d.radius x) (hr0 : d.radius x ≠ 0) :
    (∑ j : I,frameCoordinateLinear d.γ d.frame x j b*scaledFrameLogRadius d.radius d.frame j x)=
      fderiv ℝ d.radius x b := by
  have hReconstruct := frameCoordinateLinear_reconstruct d.γ d.frame x b hFrame
  have hL := congrArg (fderiv ℝ (fun y => Real.log (d.radius y)) x) hReconstruct
  simp only [map_sum,map_smul,smul_eq_mul] at hL
  calc
    _ = d.radius x*(∑ j : I,frameCoordinateLinear d.γ d.frame x j b*
        fderiv ℝ (fun y => Real.log (d.radius y)) x (d.frame x j)) := by
      simp only [scaledFrameLogRadius,Fin.sum_univ_three]
      ring
    _ = d.radius x*fderiv ℝ (fun y => Real.log (d.radius y)) x b := by rw [hL]
    _ = fderiv ℝ d.radius x b := by
      rw [logRadius_derivative d.radius x b hr hr0]
      field_simp

/-- The actual physical coframe correction is a first radial correction
against the physical normal multiplier, plus the true radius derivative.
Both arbitrary frame indices have been contracted exactly. -/
theorem physicalFirstCorrectionCoarseFamily_normal_form (d : Data) (x b : X)
    (hFrame : ∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hr : DifferentiableAt ℝ d.radius x) (hr0 : d.radius x ≠ 0) :
    physicalFirstCorrectionCoarseFamily d b x =
      (firstRadialAdjointOperatorMapL (firstDensityLogCovector d x)).comp (actualCoframeNormalSobolevL 1 d b x)+
        fderiv ℝ d.radius x b • firstRadialAdjointOperatorMapL (firstDensityLogCovector d x) := by
  rw [physicalFirstCorrectionCoarseFamily_eq]
  simp_rw [firstFrameCorrectionCoarseFamily_first_radial_form]
  have hSum : (∑ j : I,frameCoordinateLinear d.γ d.frame x j b •
      ((firstRadialAdjointOperatorMapL (firstDensityLogCovector d x)).comp (coordinateMultiplierSobolevL 1 j)+
        scaledFrameLogRadius d.radius d.frame j x • firstRadialAdjointOperatorMapL (firstDensityLogCovector d x))) =
      (firstRadialAdjointOperatorMapL (firstDensityLogCovector d x)).comp
        (∑ j : I,frameCoordinateLinear d.γ d.frame x j b • coordinateMultiplierSobolevL 1 j)+
        (∑ j : I,frameCoordinateLinear d.γ d.frame x j b*scaledFrameLogRadius d.radius d.frame j x) •
          firstRadialAdjointOperatorMapL (firstDensityLogCovector d x) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [_root_.sum_apply,_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.comp_apply,
      map_sum,map_smul,smul_add,smul_smul,Finset.sum_add_distrib,Finset.sum_smul]
  rw [hSum,coframe_scaled_log_radius_sum d x b hFrame hr hr0]
  congr 2
  simp only [actualCoframeNormalSobolevL,frameCoordinateLinear_apply]

end ShrinkingSpheres
