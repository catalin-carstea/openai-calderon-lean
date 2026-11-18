import Proof.FirstConormalCoefficientDerivative
import Proof.CommonSupportLowRadialRegularity
import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The actual first low radial correction with the same raw coefficient
    and actual normal multiplier used by the conormal family. -/
def commonSupportLowFirstRadialL
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1) (S1 : Set X) (hS1 : IsCompact S1)
    (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0) (c : ℝ) (p : P) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  c⁻¹ • (weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)-
    (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 p)).comp fixedLowRadialL)

/-- The actual first low radial derivative follows from the actual first
    energy and normal multiplier derivatives with their shared witnesses. -/
theorem commonSupport_lowFirstRadial_derivative
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1) (S1 : Set X) (hS1 : IsCompact S1)
    (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0) (c : ℝ) (x : P)
    (CI DE DM : ℝ) (hCI : 0 ≤ CI) (hDE : 0 ≤ DE) (hDM : 0 ≤ DM)
    (hci : |c⁻¹| ≤ CI) (hNE : ‖fderiv ℝ (commonSupportFullWeakEnergy a1 ha1) x‖ ≤ DE)
    (hNM : ‖fderiv ℝ (fun p => negativeBoundaryCoefficientMulL
      (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 p)) x‖ ≤ DM) :
    DifferentiableAt ℝ (commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c) x ∧
    ‖fderiv ℝ (commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c) x‖ ≤
      CI*(sphereSurfaceMass⁻¹*‖fixedHarmonicH1LiftL‖^2*DE+DM*‖fixedLowRadialL‖) := by
  let N1 := fun p => weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)
  let M1 := fun p => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 p)
  have hE := (contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) x
  have hNTheorem := commonSupport_weakFirstConormal_coefficient_derivative a1 ha1 c x hE DE hDE hNE
  obtain ⟨hN1,hDN1⟩ := hNTheorem
  have hM1 := (contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a1 ha1 S1 hS1 hz1).differentiable (by simp) x
  have hMDiff : DifferentiableAt ℝ (fun p => (M1 p).comp fixedLowRadialL) x := hM1.clm_comp (differentiableAt_const _)
  have hMD := norm_fderiv_clm_comp_le M1 (fun _ : P => fixedLowRadialL) x hM1 (differentiableAt_const _)
  simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero] at hMD
  have hMN : ‖fderiv ℝ (fun p => (M1 p).comp fixedLowRadialL) x‖ ≤ DM*‖fixedLowRadialL‖ :=
    hMD.trans (mul_le_mul_of_nonneg_right hNM (norm_nonneg _))
  have hInside := hN1.sub hMDiff
  have hInsideD := (hN1.hasFDerivAt.sub hMDiff.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => N1 p-(M1 p).comp fixedLowRadialL) x = _ at hInsideD
  have hInsideN : ‖fderiv ℝ (fun p => N1 p-(M1 p).comp fixedLowRadialL) x‖ ≤
      sphereSurfaceMass⁻¹*‖fixedHarmonicH1LiftL‖^2*DE+DM*‖fixedLowRadialL‖ := by
    rw [hInsideD]
    exact (norm_sub_le _ _).trans (add_le_add hDN1 hMN)
  refine ⟨hInside.const_smul c⁻¹,?_⟩
  have hD := (hInside.hasFDerivAt.const_smul c⁻¹).fderiv
  change fderiv ℝ (commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c) x = _ at hD
  rw [hD,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul hci hInsideN (norm_nonneg _) hCI

end ShrinkingSpheres
