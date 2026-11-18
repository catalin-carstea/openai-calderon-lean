import Proof.WeakConormalTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
attribute [local irreducible] nativeWeakHalfLift weakFirstPoissonVariationL
  nativeWeakConormalEndpoint weakFirstConormalVariationL

lemma flatConormal_eq_harmonic_energy (c : ℝ) :
    c • fixedLowRadialL = (sphereSobolevDualRieszL (1/2:ℝ)).comp
      (sphereSurfaceMass⁻¹ • (TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp
        fixedHarmonicH1LiftL fixedHarmonicH1LiftL) := by
  have hN0 := nativeWeakConormal_flat_eq_smul c
  change nativeWeakConormalEndpoint (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
    sphereFischerInner = c • fixedLowRadialL at hN0
  have hP0 := nativeWeakHalfLift_flat_eq c (flatCoefficientBound c)
  have hChange := congrArg (fun P : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 =>
    (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
      (TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp P fixedHarmonicH1LiftL)) hP0
  exact hN0.symm.trans ((nativeWeakConormal_eq_full_energy
    (a:=fun _ : X => c • (1:Mat)) (flatCoefficientBound c)).trans hChange)

private lemma conormalTaylorAssembly_sub {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : (H →L[ℝ] ℝ) →L[ℝ] G) (B B0 B1 : H →L[ℝ] H →L[ℝ] ℝ) (a r : ℝ) :
    S.comp (a • B)-S.comp (a • B0)-r • S.comp (a • B1) =
      S.comp (a • (B-B0-r • B1)) := by
  simp only [smul_sub,smul_smul,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
  module

/-- The actual conormal Taylor remainder is exactly the same native
    energy/Poisson Taylor remainder, before any derivative is estimated. -/
theorem nativeWeakConormal_first_remainder_eq_energy {a a1 : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (c r : ℝ) :
    nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner-c • fixedLowRadialL-
      r • weakFirstConormalVariationL c a1 ha1 =
      (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
        ((TauCeti.PDE.energyFormH1L ha).bilinearComp (nativeWeakHalfLift a 0 0 ha sphereFischerInner) fixedHarmonicH1LiftL-
          (TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL-
          r • ((TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp
            (weakFirstPoissonVariationL c a1 ha1) fixedHarmonicH1LiftL+
            (TauCeti.PDE.energyFormH1L ha1).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL))) := by
  have hN := nativeWeakConormal_eq_full_energy (a:=a) ha
  have hFlat := flatConormal_eq_harmonic_energy c
  have hFirst : weakFirstConormalVariationL c a1 ha1 =
      (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
        ((TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp
          (weakFirstPoissonVariationL c a1 ha1) fixedHarmonicH1LiftL+
          (TauCeti.PDE.energyFormH1L ha1).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL)) := by
    unfold weakFirstConormalVariationL
    rfl
  have hSub := congrArg₂ (fun N N0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => N-N0) hN hFlat
  have hStart := congrArg₂ (fun L R : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => L-r • R) hSub hFirst
  exact hStart.trans (conormalTaylorAssembly_sub (sphereSobolevDualRieszL (1/2:ℝ))
    ((TauCeti.PDE.energyFormH1L ha).bilinearComp (nativeWeakHalfLift a 0 0 ha sphereFischerInner) fixedHarmonicH1LiftL)
    ((TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL)
    ((TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp
      (weakFirstPoissonVariationL c a1 ha1) fixedHarmonicH1LiftL+
      (TauCeti.PDE.energyFormH1L ha1).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL) sphereSurfaceMass⁻¹ r)


end ShrinkingSpheres
