import Proof.EuclideanWeakPoisson
import Proof.FullWeakEnergyContinuity

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
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeCoefficientWeakFunctionalInverse nativeCoefficientWeakEnergyL
  OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion

/-- The weak half-order Poisson lift differs from the flat Euclidean lift by
    the coefficient C0 error times the actual weak inverse bound. -/
theorem norm_nativeWeakHalfLift_sub_flat_le {a : X → Mat} (c : ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hcoeff0 : MemLp (fun _ : X => TauCeti.PDE.energyIntegrand (c • (1:Mat)) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hInv : ‖nativeCoefficientWeakFunctionalInverse a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff‖ ≤ C)
    (hDiff : ∀ x ∈ (ballOpens : Set X),∀ i j,|a x i j-(c • (1:Mat)) i j| ≤ q) :
    ‖nativeWeakHalfLift a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner-
      fixedHarmonicH1LiftL‖ ≤ C*(9*q)*‖fixedHarmonicH1LiftL‖ := by
  let E := TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff
  let E0 := TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=fun _ : X => c • (1:Mat)) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff0
  let R := nativeCoefficientWeakEnergyL a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff
  let I := nativeCoefficientWeakFunctionalInverse a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff
  have hENorm : ‖E-E0‖ ≤ 9*q := norm_unitBall_full_energyForm_sub_le
    (a:=a) (a0:=fun _ : X => c • (1:Mat)) hcoeff hcoeff0 q hq hDiff
  have hRpoint (f : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
      R (fixedHarmonicH1LiftL f) v = (E-E0) (fixedHarmonicH1LiftL f) (v : BallH1) := by
    have hZero : E0 (fixedHarmonicH1LiftL f) (v : BallH1) = 0 := by
      rw [TauCeti.PDE.energyFormH1L_apply]
      exact fixedHarmonicH1Lift_flat_weak c f v
    change R (fixedHarmonicH1LiftL f) v = E (fixedHarmonicH1LiftL f) (v : BallH1)-
      E0 (fixedHarmonicH1LiftL f) (v : BallH1)
    have hMain : R (fixedHarmonicH1LiftL f) v = E (fixedHarmonicH1LiftL f) (v : BallH1) :=
      (nativeCoefficientWeakEnergyL_apply a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff (fixedHarmonicH1LiftL f) v).trans
        (TauCeti.PDE.energyFormH1L_apply (mu:=(volume:Measure X)) (Omega:=ballOpens)
          (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff _ _).symm
    exact hMain.trans (sub_eq_self.mpr hZero).symm
  have hRNorm (f : SphereSobolev (1/2:ℝ)) :
      ‖R (fixedHarmonicH1LiftL f)‖ ≤ (9*q)*‖fixedHarmonicH1LiftL f‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (norm_nonneg _))
    intro v
    rw [hRpoint]
    exact ((E-E0).le_opNorm₂ (fixedHarmonicH1LiftL f) (v : BallH1)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hENorm (norm_nonneg _)) (norm_nonneg _))
  have hNative (f : SphereSobolev (1/2:ℝ)) :
      nativeWeakHalfLift a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner f =
      fixedHarmonicH1LiftL f-(I (R (fixedHarmonicH1LiftL f)) : BallH1) := by
    have hEq := congrArg (fun S : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 => S f)
      (nativeWeakHalfLift_eq_affineAssembly a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner)
    exact hEq.trans (nativeWeakAffineLiftAssembly_apply
      (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL I R fixedHarmonicH1LiftL f)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hC (by positivity)) (norm_nonneg _))
  intro f
  change ‖nativeWeakHalfLift a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner f-
    fixedHarmonicH1LiftL f‖ ≤ _
  rw [hNative]
  have hCancel (u v : BallH1) : u-v-u = -v := by abel
  rw [hCancel,norm_neg]
  change ‖I (R (fixedHarmonicH1LiftL f))‖ ≤ _
  calc
    _ ≤ ‖I‖*‖R (fixedHarmonicH1LiftL f)‖ := I.le_opNorm _
    _ ≤ C*‖R (fixedHarmonicH1LiftL f)‖ := mul_le_mul_of_nonneg_right hInv (norm_nonneg _)
    _ ≤ C*((9*q)*‖fixedHarmonicH1LiftL f‖) := mul_le_mul_of_nonneg_left (hRNorm f) hC
    _ ≤ C*((9*q)*(‖fixedHarmonicH1LiftL‖*‖f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (fixedHarmonicH1LiftL.le_opNorm f) (by positivity)) hC
    _ = _ := by ring

/-- The weak native lift for a scalar flat coefficient is exactly the completed
    Euclidean Poisson lift, independently of the chosen inverse implementation. -/
theorem nativeWeakHalfLift_flat_eq (c : ℝ)
    (hcoeff : MemLp (fun _ : X => TauCeti.PDE.energyIntegrand (c • (1:Mat)) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens)) :
    nativeWeakHalfLift (fun _ : X => c • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner =
      fixedHarmonicH1LiftL := by
  let I := nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat))
    (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff
  have hb := norm_nativeWeakHalfLift_sub_flat_le (a:=fun _ : X => c • (1:Mat)) c hcoeff hcoeff
    ‖I‖ 0 (norm_nonneg _) le_rfl le_rfl (fun x hx i j => by simp)
  have hZero : ‖nativeWeakHalfLift (fun _ : X => c • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner-
      fixedHarmonicH1LiftL‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa only [mul_zero,zero_mul] using hb
  exact sub_eq_zero.mp (norm_eq_zero.mp hZero)

end ShrinkingSpheres
