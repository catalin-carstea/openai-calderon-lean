import Proof.NativeBoundaryCalculus
import Proof.StrongHarmonicCorrection
import Proof.FlatFullCoefficientOperator
import Proof.UniformActualCoefficientPerturbation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- A locally small C1 principal-coefficient perturbation gives a small H2
    correction for genuine smooth harmonic representatives. -/
theorem norm_smooth_harmonic_correction_of_local_C1 {a : X → Mat} {C : ℝ}
    (hC : 0 ≤ C)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X))
      (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff))
    (hLifts : StrongDirichletLiftData a C)
    (F F0 : SmoothCoefficientMatrix 2) (c q : ℝ) (hq : 0 ≤ q)
    (hPoint : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = a x)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ q)
    (U V : SmoothData)
    (hBoundary : ∀ x : X,‖x‖ = 1 → U.1 x = V.1 x)
    (hWeak : ∀ v : BallH1Zero,TauCeti.PDE.energyFormH1 a
      (fun _ => (0:X)) (fun _ => (0:ℝ)) (smoothSobolev U) (v : BallH1) = 0)
    (hFlat : fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0) (smoothBallSobolev 2 V) = 0) :
    ‖smoothBallSobolev 2 U-smoothBallSobolev 2 V‖ ≤
      C*fullC1OperatorBudget fixedSobolevCalculus*q*‖smoothBallSobolev 2 V‖ := by
  let f := -fullCoefficientOperatorL fixedSobolevCalculus 0 (F-c • F0) (smoothBallSobolev 2 V)
  have hOp : fullCoefficientOperatorL fixedSobolevCalculus 0 (F-c • F0) (smoothBallSobolev 2 V) =
      fullCoefficientOperatorL fixedSobolevCalculus 0 F (smoothBallSobolev 2 V) := by
    simp only [map_sub,_root_.sub_apply,hFlat,sub_zero]
  have hForcing (v : BallH1Zero) : TauCeti.PDE.dirichletForcing
      (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (TauCeti.Wkp.value (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0 f) v =
      -TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ))
        (smoothSobolev V) (v : BallH1) := by
    have hE := fullCoefficientOperator_energy fixedSobolevCalculus 0 F (smoothBallSobolev 2 V) v
    rw [firstOrder_smoothBallSobolev] at hE
    have hTransfer := energyFormH1_congr_coeff_on hPoint (smoothSobolev V) (v : BallH1)
    have hEnergy := hE.trans hTransfer
    dsimp only [f]
    rw [hOp,← TauCeti.Wkp.valueL_apply,map_neg,TauCeti.Wkp.valueL_apply,
      TauCeti.PDE.dirichletForcing_apply,inner_neg_left,
      ← TauCeti.PDE.dirichletForcing_apply]
    exact congrArg Neg.neg hEnergy
  have hNorm := norm_smooth_harmonic_correction_le (a:=a) hcoeff hc hLifts U V hBoundary hWeak f hForcing
  have hOpBound := norm_fullCoefficientOperator_zero_le fixedSobolevCalculus (F-c • F0) q hq hValue hDerivative
  have hFBound : ‖f‖ ≤ (fullC1OperatorBudget fixedSobolevCalculus*q)*‖smoothBallSobolev 2 V‖ := by
    dsimp only [f]
    rw [norm_neg]
    exact ((fullCoefficientOperatorL fixedSobolevCalculus 0 (F-c • F0)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hOpBound (norm_nonneg _))
  exact hNorm.trans ((mul_le_mul_of_nonneg_left hFBound hC).trans_eq (by ring))

end ShrinkingSpheres
