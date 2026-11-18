import Proof.FirstConormalGreen
import Proof.UniformLowRadialTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- The scalar affine first coefficient has only a normal boundary flux.
    Its tangential coefficient vanishes exactly. -/
theorem firstCoefficient_conormal_high (F1 : SmoothCoefficientMatrix 2) (q : X → ℝ)
    (hF1 : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = q w.val • (1:Mat))
    (f : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (ordinaryConormalTraceL fixedSobolevCalculus fixedUnitBallValueTrace F1 (fixedHarmonicLiftL f))) =
      negativeBoundaryCoefficientMulL (normalCoefficientJet F1)
        (fixedLowRadialL (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) := by
  have h := nativeH2_conormal_negativeHalf_eq_coefficient_normal_add_tangent
    fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    fixedUnitBallValueTrace F1 (normalCoefficientJet F1) (tangentCoefficientJet F1)
    (coefficientSmoothData_normalCoefficientJet F1) (coefficientSmoothData_tangentCoefficientJet F1)
    (fixedHarmonicLiftL f)
  have hT (j : I) : negativeBoundaryCoefficientMulL (tangentCoefficientJet F1 j) = 0 :=
    negativeTangentCoefficient_scalar_zero F1 q hF1 j
  change _ = negativeBoundaryCoefficientMulL (normalCoefficientJet F1)
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (fixedHarmonicLiftL f))))+
    ∑ j : I,negativeBoundaryCoefficientMulL (tangentCoefficientJet F1 j) _ at h
  simp only [hT,ContinuousLinearMap.zero_apply,Finset.sum_const_zero,add_zero] at h
  exact h.trans (congrArg (negativeBoundaryCoefficientMulL (normalCoefficientJet F1))
    (fixedLowRadialL_high f).symm)

/-- The low and high first radial variations are restrictions of the same
    operator. This uses the actual first solution and first coefficient fluxes. -/
theorem lowFirstRadialVariation_high_compatible (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : 0 < c)
    (hF0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 x = 1)
    (q : X → ℝ)
    (hF1 : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = q w.val • (1:Mat))
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    lowFirstRadialVariationL c F1 ha1
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (highFirstRadialVariationL F0 F1 c f) := by
  let g := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U1 := strongFirstPoissonVariationL F0 F1 c f
  let M1 := negativeBoundaryCoefficientMulL (normalCoefficientJet F1)
  let R := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    (fixedHalfOutwardTraceL U1)
  have hFlat (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (c • F0) x = c • (1:Mat) := by
    rw [coefficientMatrixField_smul,hF0 x hx]
  have hN := weakFirstConormal_high_flux F0 F1 c hc hF0 ha1 hInv0 f
  rw [ordinaryConormalTraceL_flat (c • F0) c hFlat U1] at hN
  simp only [map_add,map_smul] at hN
  have hCoeff := firstCoefficient_conormal_high F1 q hF1 f
  have hRad := negative_inclusion_halfOutwardTrace U1
  have hMain : weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1 g =
      c • R+M1 (fixedLowRadialL g) :=
    hN.trans (congrArg₂ (fun u v : SphereSobolev (-(1/2:ℝ)) => c • u+v) hRad.symm hCoeff)
  change c⁻¹ • (weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1 g-
    M1 (fixedLowRadialL g)) = R
  have hChange := congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => c⁻¹ • (z-M1 (fixedLowRadialL g))) hMain
  exact hChange.trans (by rw [add_sub_cancel_right,smul_smul,inv_mul_cancel₀ hc.ne',one_smul])

end ShrinkingSpheres
