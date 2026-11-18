import Proof.FirstMultiplierRadialGraph
import Proof.BoundarySmoothMultiplier
import Proof.RadialCorrectionLinear
import Proof.Archive.SphereCoefficientMultiplierCLM

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier

/-- The actual gained first variation agrees in L2 with the commutator of
exactly the canonical bounded radial correction for the scalar affine model. -/
theorem halfMultiplierFirstVariation_canonical_graph (F0 F1 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc0 : IsCoercive (TauCeti.PDE.energyFormH1L0 ha0))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (ell : X →L[ℝ] ℝ)
    (hF1 : ∀ z ∈ (ballOpens:Set X),∀ i j,coefficientValue 2 (F1 i j) z = ell z*(1:Mat) i j)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (halfMultiplierFirstVariationL F0 F1 ha1 Q (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) =
    radialCorrectionCovectorL ell
      (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
        (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) f))-
    coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
      (radialCorrectionCovectorL ell (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) f)) := by
  let R := highFirstRadialVariationL F0 F1 1
  let M3 := nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  let M1 := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  let M0 := coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
  let I0 := sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
  let J0 := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  have hB : coarseFirstRadialVariationL 1 ell = radialCorrectionCovectorL ell := by
    simpa only [inv_one,one_smul] using coarseFirstRadialVariationL_normalized_covector 1 ell
  have hR (v : SphereSobolev (3/2:ℝ)) : J0 (R v) = radialCorrectionCovectorL ell (I0 v) := by
    have h := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T v)
      (highFirstRadialVariation_coarse_eq F0 F1 1 (by norm_num) ell hFlat hF1
        (by simpa only [one_smul] using hInv0))
    simpa only [ContinuousLinearMap.comp_apply,hB] using h
  have hM3 : I0 (M3 f) = M0 (I0 f) := sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero
    fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q f
  have hM1 : J0 (M1 (R f)) = M0 (J0 (R f)) := sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue
    fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
    Q (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm (R f)
  rw [halfMultiplierFirstVariation_high F0 F1 ha0 ha1 hc0 hFlat hInv0 Q f,map_sub]
  change J0 (R (M3 f))-J0 (M1 (R f)) = _
  rw [hM1,hR (M3 f),hR f,hM3]

end ShrinkingSpheres
