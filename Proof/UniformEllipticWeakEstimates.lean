import Proof.NativeWeakInverseBound
import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Shared native weak estimates from the actual coefficient ellipticity.
    This is the common derivation for metric, flat and normalized coefficients. -/
theorem exists_native_weak_estimates_of_uniformlyElliptic (a : X → Mat) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) a lam Lam)
    (hMeas : AEStronglyMeasurable a ((volume:Measure X).restrict ballOpens)) :
    ∃ hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens),
      IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff) ∧
      ‖nativeCoefficientWeakFunctionalInverse a 0 0 hcoeff‖ ≤ 5*lam⁻¹ ∧
      ‖TauCeti.PDE.energyFormH1L hcoeff‖ ≤ Lam := by
  let hcoeff := memLp_zeroDriftEnergyIntegrand hUE hMeas
  refine ⟨hcoeff,isCoercive_unitBall_zeroDrift hUE hMeas hcoeff,?_,?_⟩
  · have hα : 0 < lam/5 := div_pos hUE.pos (by norm_num)
    have hLower (u : BallH1Zero) : (lam/5)*‖u‖*‖u‖ ≤
        TauCeti.PDE.energyFormH1 a 0 0 (u:BallH1) (u:BallH1) :=
      (unitBall_zeroDrift_coercivity hUE hMeas hcoeff u).trans_eq (TauCeti.PDE.energyFormH1L0_apply hcoeff u u)
    exact (norm_nativeCoefficientWeakFunctionalInverse_le hcoeff (lam/5) hα hLower).trans_eq (by field_simp)
  · have hn := TauCeti.PDE.norm_energyFormH1L_le_of_bounds (Lam:=Lam) (beta:=0) (gamma:=0)
      hcoeff hUE.upper_nonneg (fun x hx => hUE.upper_bound hx) le_rfl le_rfl
      (fun _ _ => by simp) (fun _ _ => by simp)
    simpa only [add_zero] using hn

end ShrinkingSpheres
