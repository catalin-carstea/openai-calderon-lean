import Proof.UniformWeakPoissonTaylor
import Proof.EnergyConormalTaylorBound
import Proof.FlatConormalRadialTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments

/-- The conormal first variation retains both the varying solution and varying
    coefficient energy terms. -/
def weakFirstConormalVariationL (c : ℝ) (a1 : X → Mat)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
    ((TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp
      (weakFirstPoissonVariationL c a1 ha1) fixedHarmonicH1LiftL+
    (TauCeti.PDE.energyFormH1L ha1).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL))

lemma nativeWeakConormal_eq_full_energy {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner =
      (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
        (TauCeti.PDE.energyFormH1L ha).bilinearComp (nativeWeakHalfLift a 0 0 ha sphereFischerInner) fixedHarmonicH1LiftL) := rfl

private theorem conormalAssembly_sub {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : (H →L[ℝ] ℝ) →L[ℝ] G) (B B0 B1 : H →L[ℝ] H →L[ℝ] ℝ) (a r : ℝ) :
    S.comp (a • B)-S.comp (a • B0)-r • S.comp (a • B1) =
      S.comp (a • (B-B0-r • B1)) := by
  simp only [smul_sub,smul_smul,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
  module

/-- The actual weak conormal endpoint has a quadratic first Taylor remainder
    from the shared actual weak energy and Poisson witnesses. -/
theorem NativeWeakTaylorData.conormal_remainder_bound {a a1 : X → Mat} {c r CW DA P Q CP1 CP2 : ℝ}
    (h : NativeWeakTaylorData a a1 c r CW DA P Q CP1 CP2)
    (hr : 0 ≤ r) (hDA : 0 ≤ DA) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hCP1 : 0 ≤ CP1) (hCP2 : 0 ≤ CP2) :
    ‖nativeWeakConormalEndpoint a 0 0 h.energy.coefficient_bound sphereFischerInner-
      c • fixedLowRadialL-r • weakFirstConormalVariationL c a1 h.first_coefficient_bound‖ ≤
      sphereSurfaceMass⁻¹*((DA*CP2+(9*P+9*Q)*CP1+9*Q*‖fixedHarmonicH1LiftL‖)*‖fixedHarmonicH1LiftL‖)*r^2 := by
  let E := TauCeti.PDE.energyFormH1L h.energy.coefficient_bound
  let E0 := TauCeti.PDE.energyFormH1L (flatCoefficientBound c)
  let E1 := TauCeti.PDE.energyFormH1L h.first_coefficient_bound
  let Pa := nativeWeakHalfLift a 0 0 h.energy.coefficient_bound sphereFischerInner
  let P0 := fixedHarmonicH1LiftL
  let P1 := weakFirstPoissonVariationL c a1 h.first_coefficient_bound
  have hFlat : c • fixedLowRadialL = (sphereSobolevDualRieszL (1/2:ℝ)).comp
      (sphereSurfaceMass⁻¹ • E0.bilinearComp P0 P0) := by
    have hN0 := nativeWeakConormal_flat_eq_smul c
    change nativeWeakConormalEndpoint (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
      sphereFischerInner = c • fixedLowRadialL at hN0
    have hP0 := nativeWeakHalfLift_flat_eq c (flatCoefficientBound c)
    have hChange := congrArg (fun P : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 =>
      (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ • E0.bilinearComp P P0)) hP0
    exact hN0.symm.trans ((nativeWeakConormal_eq_full_energy
      (a:=fun _ : X => c • (1:Mat)) (flatCoefficientBound c)).trans hChange)
  have hN := nativeWeakConormal_eq_full_energy (a:=a) h.energy.coefficient_bound
  have hStart := congrArg₂ (fun N N0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    N-N0-r • weakFirstConormalVariationL c a1 h.first_coefficient_bound) hN hFlat
  have hAlg := conormalAssembly_sub (sphereSobolevDualRieszL (1/2:ℝ))
    (E.bilinearComp Pa P0) (E0.bilinearComp P0 P0)
    (E0.bilinearComp P1 P0+E1.bilinearComp P0 P0) sphereSurfaceMass⁻¹ r
  have hEq := hStart.trans hAlg
  have hBound := norm_conormal_energy_taylor_le E E0 E1 Pa P0 P1 r DA (9*P) (9*Q) CP2 CP1 hr hDA
    (by positivity) (by positivity) hCP2 hCP1 h.energy.energy_bound h.first_energy_bound h.energy_remainder_bound
    h.poisson_remainder_bound h.first_poisson_bound h.energy_difference_bound
  have hNorm := congrArg (fun N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => ‖N‖) hEq
  exact hNorm.symm ▸ hBound

end ShrinkingSpheres
