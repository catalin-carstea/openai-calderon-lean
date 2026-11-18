import Proof.FirstMultiplierRadialGraph
import Proof.UniformNormalizedMultiplierTaylor

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

lemma strongPoissonL_flat_coefficient (F0 : SmoothCoefficientMatrix 2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1) :
    strongPoissonL F0 = fixedHarmonicLiftL := by
  apply ContinuousLinearMap.ext
  intro f
  have h := fullCoefficientOperator_flat_harmonicLift fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    F0 hFlat 1 f
  simp only [one_smul] at h
  change fullCoefficientOperatorL fixedSobolevCalculus 0 F0 (fixedHarmonicLiftL f) = 0 at h
  rw [strongPoissonL_apply,h,map_zero]
  simp only [ZeroMemClass.coe_zero,sub_zero]

lemma flat_compact_coefficient_energy_coercive (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1) :
    IsCoercive (TauCeti.PDE.energyFormH1L0 ha0) := by
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (coefficientMatrixField 2 F0) 1 1 := by
    simpa only [one_smul] using uniformlyEllipticOn_flat_coefficientMatrix F0 1 (by norm_num) hFlat
  obtain ⟨ha,hc,hI,hE⟩ := exists_native_weak_estimates_of_uniformlyElliptic (coefficientMatrixField 2 F0) 1 1 hUE
    (aestronglyMeasurable_coefficientMatrixField 2 F0)
  exact hc

def radialTaylorMultiplierCommutatorL (F F0 F1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) (r : ℝ) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  halfRadialMultiplierCommutatorL F ha Q-halfRadialMultiplierCommutatorL F0 ha0 Q-
    r • halfMultiplierFirstVariationL F0 F1 ha1 Q

/-- The gained bounded operator is the commutator of the ACTUAL high
radial Taylor remainder, on its entire high boundary domain. -/
theorem radialTaylorMultiplierCommutator_high (F F0 F1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : SmoothCoefficientJets 3) (r : ℝ) (f : SphereSobolev (3/2:ℝ)) :
    radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
    (actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 1)
      (nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace Q f)-
    nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
      ((actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 1) f) := by
  have hc0 := flat_compact_coefficient_energy_coercive F0 ha0 hFlat
  simp only [radialTaylorMultiplierCommutatorL,sub_apply,smul_apply]
  rw [halfRadialMultiplierCommutatorL_high F ha hc hInv,
    halfRadialMultiplierCommutatorL_high F0 ha0 hc0 hInv0,
    halfMultiplierFirstVariation_high F0 F1 ha0 ha1 hc0 hFlat hInv0,
    strongPoissonL_flat_coefficient F0 hFlat]
  simp only [actualHighRadialErrorL,highFirstRadialVariationL,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    map_sub,map_smul]
  module

end ShrinkingSpheres
