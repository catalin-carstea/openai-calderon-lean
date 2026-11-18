import Proof.UniformNormalizedRadialMultiplierGain
import Proof.Archive.NativeHarmonicHalfCoarseDualPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

/-- The actual gained commutator has its balanced half/negative-half
quadratic pairing bound on the same all-H1 domain. -/
theorem RadialMultiplierGainData.pairing_bound
    {F F0 F1 : SmoothCoefficientMatrix 2}
    {ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)}
    {ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)}
    {ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)}
    {ell : X →L[ℝ] ℝ} {Qm : SmoothCoefficientJets 3} {r C : ℝ}
    (t : RadialMultiplierGainData F F0 F1 ha ha0 ha1 ell Qm r C)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hHigh : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F) =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (u : SphereSobolev 1) (z : SphereSobolev 0) :
    |⟪(R-r • ((radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))))
        (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Qm) u)-
      coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Qm))
        ((R-r • ((radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num)))) u),z⟫_ℝ| ≤
    (C*r^2)*‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u‖*
      ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) z‖ := by
  let G := radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Qm r
  let f := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u
  let v := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) z
  have hGraph := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u) (t.midpoint_graph R hHigh)
  have hPair := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) (G f) z
  have hNorm : ‖G f‖ ≤ (C*r^2)*‖f‖ := (G.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right t.norm_bound (norm_nonneg _))
  have hBound := (abs_sphereSobolevDualPairing_le (1/2:ℝ) (G f) v).trans
    (mul_le_mul_of_nonneg_right hNorm (norm_nonneg v))
  rw [hPair] at hBound
  exact (congrArg (fun w : SphereSobolev 0 => |⟪w,z⟫_ℝ|) hGraph).symm.trans_le hBound

end ShrinkingSpheres
