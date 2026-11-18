import Proof.WeakPoissonComparison
import Proof.BilinearPoissonComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion

/-- C0 bulk coefficient perturbations control the weak conormal endpoint
    H1/2 -> H-1/2 through the actual weak inverse and energy bounds. -/
theorem norm_nativeWeakConormal_sub_flat_le {a : X → Mat} (c : ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hcoeff0 : MemLp (fun _ : X => TauCeti.PDE.energyIntegrand (c • (1:Mat)) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (C D q : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hInv : ‖nativeCoefficientWeakFunctionalInverse a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff‖ ≤ C)
    (hEnergy : ‖TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X))
      (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff‖ ≤ D)
    (hDiff : ∀ x ∈ (ballOpens : Set X),∀ i j,|a x i j-(c • (1:Mat)) i j| ≤ q) :
    ‖nativeWeakConormalEndpoint a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner-
      nativeWeakConormalEndpoint (fun _ : X => c • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff0 sphereFischerInner‖ ≤
      sphereSurfaceMass⁻¹*((D*C+1)*(9*q)*‖fixedHarmonicH1LiftL‖^2) := by
  let E := TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff
  let E0 := TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=fun _ : X => c • (1:Mat)) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff0
  let P := fixedHarmonicH1LiftL
  let Pa := nativeWeakHalfLift a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner
  let Φ := nativeWeakConormalEndpointFunctional a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner
  let Φ0 := nativeWeakConormalEndpointFunctional (fun _ : X => c • (1:Mat)) (fun _ => (0:X))
    (fun _ => (0:ℝ)) hcoeff0 sphereFischerInner
  have hDeltaE : ‖E-E0‖ ≤ 9*q := norm_unitBall_full_energyForm_sub_le
    (a:=a) (a0:=fun _ : X => c • (1:Mat)) hcoeff hcoeff0 q hq hDiff
  have hDeltaP : ‖Pa-P‖ ≤ C*(9*q)*‖P‖ :=
    norm_nativeWeakHalfLift_sub_flat_le c hcoeff hcoeff0 C q hC hq hInv hDiff
  have hBi := norm_bilinear_poisson_difference_le E E0 Pa P C D (9*q) hC hD (by positivity)
    hEnergy hDeltaE hDeltaP
  have hΦ : Φ-Φ0 = sphereSurfaceMass⁻¹ • (E.bilinearComp Pa P-E0.bilinearComp P P) := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousLinearMap.ext
    intro z
    simp only [_root_.sub_apply,_root_.smul_apply,ContinuousLinearMap.bilinearComp_apply]
    rw [nativeWeakConormalEndpointFunctional_apply,nativeWeakConormalEndpointFunctional_apply,
      nativeWeakHalfLift_flat_eq c hcoeff0]
    simp only [E,E0,Pa,P,fixedHarmonicH1LiftL,TauCeti.PDE.energyFormH1L_apply,smul_eq_mul]
    ring
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hΦBound : ‖Φ-Φ0‖ ≤ sphereSurfaceMass⁻¹*((D*C+1)*(9*q)*‖P‖^2) := by
    exact (congrArg norm hΦ).le.trans
      (norm_nonneg_smul_bilinear_le (F:=SphereSobolev (1/2:ℝ)) sphereSurfaceMass⁻¹ hArea
        (E.bilinearComp Pa P-E0.bilinearComp P P) _ hBi)
  have hRiesz : ‖sphereSobolevDualRieszL (1/2:ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ell
    rw [norm_sphereSobolevDualRieszL_apply,one_mul]
  have hEndpoint : nativeWeakConormalEndpoint a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner-
      nativeWeakConormalEndpoint (fun _ : X => c • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff0 sphereFischerInner =
      (sphereSobolevDualRieszL (1/2:ℝ)).comp (Φ-Φ0) := by
    apply ContinuousLinearMap.ext
    intro f
    change sphereSobolevDualRieszL (1/2:ℝ) (Φ f)-sphereSobolevDualRieszL (1/2:ℝ) (Φ0 f) =
      sphereSobolevDualRieszL (1/2:ℝ) (Φ f-Φ0 f)
    exact ((sphereSobolevDualRieszL (1/2:ℝ)).map_sub _ _).symm
  rw [hEndpoint]
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hRiesz (norm_nonneg _)).trans_eq (one_mul _))).trans hΦBound

end ShrinkingSpheres
