import Proof.UniformActualStrongLifts
import Proof.StrongPoissonPerturbation
import Proof.WeakTraceUniqueness

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
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- The completed Poisson correction solves the actual weak energy equation. -/
theorem strongPoissonL_weak {a : X → Mat} (F : SmoothCoefficientMatrix 2)
    (hPoint : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = a x)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ))
      (TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) (v : BallH1) = 0 := by
  have hE := fullCoefficientOperator_energy fixedSobolevCalculus 0 F (strongPoissonL F f) v
  rw [fullCoefficientOperator_strongPoissonL F hInv f,TauCeti.Wkp.value_zero,
    TauCeti.PDE.dirichletForcing_apply,inner_zero_left] at hE
  exact (energyFormH1_congr_coeff_on hPoint
    (TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) (v : BallH1)).symm.trans hE.symm

/-- The zero-boundary correction preserves the actual fixed value trace. -/
theorem strongPoissonL_valueTrace (F : SmoothCoefficientMatrix 2) (f : SphereSobolev (3/2:ℝ)) :
    fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) =
      fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)) := by
  let w : BallH1Zero := ⟨TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)-
    TauCeti.Wkp.firstOrder 1 (strongPoissonL F f),strongPoissonL_zero_boundary_difference F f⟩
  have hZero := valueTraceL_zeroDirichlet fixedUnitBallValueTrace w
  change fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)-
    TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) = 0 at hZero
  rw [map_sub] at hZero
  exact (sub_eq_zero.mp hZero).symm

/-- A classical actual harmonic representative with the same native trace is
    precisely the completed H2 Poisson solution, not an abstract surrogate. -/
theorem strongPoissonL_eq_smooth_harmonic {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X))
      (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff))
    (F : SmoothCoefficientMatrix 2)
    (hPoint : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = a x)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (U : SmoothData)
    (hWeak : ∀ v : BallH1Zero,TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ))
      (smoothSobolev U) (v : BallH1) = 0)
    (hTrace : fixedUnitBallValueTrace.valueTraceL (smoothSobolev U) =
      fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f))) :
    smoothBallSobolev 2 U = strongPoissonL F f := by
  have hFirst := weak_harmonic_eq_of_valueTrace_eq (a:=a) hcoeff hc (smoothSobolev U)
    (TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) hWeak (strongPoissonL_weak F hPoint hInv f)
    (hTrace.trans (strongPoissonL_valueTrace F f).symm)
  have hEq : TauCeti.Wkp.firstOrder 1 (smoothBallSobolev 2 U) =
      TauCeti.Wkp.firstOrder 1 (strongPoissonL F f) := (firstOrder_smoothBallSobolev 1 U).trans hFirst
  have hValue := congrArg (fun z : BallH1 => TauCeti.W1p.value z) hEq
  simp only [TauCeti.Wkp.value_firstOrder] at hValue
  exact TauCeti.Wkp.ext 2 hValue

end ShrinkingSpheres
