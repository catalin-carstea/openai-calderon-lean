import Proof.UniformActualStrongLifts
import Proof.Archive.NativeSmoothBallSobolev
import Proof.AffineWeakEquation
import Proof.WeakDirichletCenterComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Weak uniqueness identifies the smooth physical correction with a bounded
    H2 zero-boundary lift once its L2 forcing has been identified. -/
theorem smooth_harmonic_correction_has_strong_lift {a : X → Mat} {C : ℝ}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X)) (Omega:=ballOpens) (a:=a)
      (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff))
    (hLifts : StrongDirichletLiftData a C) (U V : SmoothData)
    (hBoundary : ∀ x : X,‖x‖ = 1 → U.1 x = V.1 x)
    (hWeak : ∀ v : BallH1Zero,TauCeti.PDE.energyFormH1 a
      (fun _ => (0:X)) (fun _ => (0:ℝ)) (smoothSobolev U) (v : BallH1) = 0)
    (f : BallSobolev 0)
    (hForcing : ∀ v : BallH1Zero,TauCeti.PDE.dirichletForcing
      (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (TauCeti.Wkp.value (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0 f) v =
        -TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ))
          (smoothSobolev V) (v : BallH1)) :
    ∃ Z : StrongDirichletSpace 0,
      (strongDirichletProjectionL 0 Z : BallH1) = smoothSobolev U-smoothSobolev V ∧
      ‖Z‖ ≤ C*‖f‖ := by
  have hRaw := @StrongDirichletLiftData.solve a C hLifts f
  rcases hRaw with ⟨Z,hZ,hNorm⟩
  let B : BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ :=
    TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X)) (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff
  let ell : StrongDual ℝ BallH1Zero := affineDirichletForcing (a:=a) hcoeff (smoothSobolev V)
  have hZeq : ∀ v : BallH1Zero,B (strongDirichletProjectionL 0 Z) v = ell v := by
    intro v
    exact (TauCeti.PDE.energyFormH1L0_apply (mu:=(volume:Measure X)) (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff _ _).trans ((hZ v).trans ((hForcing v).trans
      (affineDirichletForcing_apply (a:=a) hcoeff (smoothSobolev V) v).symm))
  have hWeq : ∀ v : BallH1Zero,B (smoothBoundaryDifference U V hBoundary) v = ell v :=
    smooth_boundary_difference_equation (a:=a) hcoeff U V hBoundary hWeak
  obtain ⟨α,hα,hCoerce⟩ := hc
  have hBound := coercive_bilinear_solution_difference_bound B B α hα hCoerce hCoerce
    ell (strongDirichletProjectionL 0 Z) (smoothBoundaryDifference U V hBoundary) hZeq hWeq
  have hZero : ‖strongDirichletProjectionL 0 Z-smoothBoundaryDifference U V hBoundary‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa only [sub_self,norm_zero,mul_zero,zero_mul] using hBound
  have hEqual : strongDirichletProjectionL 0 Z = smoothBoundaryDifference U V hBoundary :=
    sub_eq_zero.mp (norm_eq_zero.mp hZero)
  exact ⟨Z,congrArg (fun z : BallH1Zero => (z : BallH1)) hEqual,hNorm⟩

/-- The strong lift controls the genuine H2 difference, since its H1 projection
    determines its L2 value and hence its H2 Sobolev element. -/
theorem norm_smooth_harmonic_correction_le {a : X → Mat} {C : ℝ}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X))
      (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff))
    (hLifts : StrongDirichletLiftData a C) (U V : SmoothData)
    (hBoundary : ∀ x : X,‖x‖ = 1 → U.1 x = V.1 x)
    (hWeak : ∀ v : BallH1Zero,TauCeti.PDE.energyFormH1 a
      (fun _ => (0:X)) (fun _ => (0:ℝ)) (smoothSobolev U) (v : BallH1) = 0)
    (f : BallSobolev 0)
    (hForcing : ∀ v : BallH1Zero,TauCeti.PDE.dirichletForcing
      (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (TauCeti.Wkp.value (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0 f) v =
        -TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ))
          (smoothSobolev V) (v : BallH1)) :
    ‖smoothBallSobolev 2 U-smoothBallSobolev 2 V‖ ≤ C*‖f‖ := by
  obtain ⟨Z,hZ,hNorm⟩ := smooth_harmonic_correction_has_strong_lift
    (a:=a) hcoeff hc hLifts U V hBoundary hWeak f hForcing
  let L := TauCeti.Wkp.firstOrderL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 1
  have hSub : L (smoothBallSobolev 2 U-smoothBallSobolev 2 V) =
      smoothSobolev U-smoothSobolev V := by
    rw [map_sub]
    exact congrArg₂ (fun x y : BallH1 => x-y)
      (firstOrder_smoothBallSobolev 1 U) (firstOrder_smoothBallSobolev 1 V)
  have hFirst : TauCeti.Wkp.firstOrder 1 (Z : BallSobolev 2) =
      TauCeti.Wkp.firstOrder 1 (smoothBallSobolev 2 U-smoothBallSobolev 2 V) :=
    hZ.trans hSub.symm
  have hValue := congrArg (fun z : BallH1 => TauCeti.W1p.value z) hFirst
  simp only [TauCeti.Wkp.value_firstOrder] at hValue
  have hEq := TauCeti.Wkp.ext 2 hValue
  rw [← hEq]
  exact hNorm

end ShrinkingSpheres
