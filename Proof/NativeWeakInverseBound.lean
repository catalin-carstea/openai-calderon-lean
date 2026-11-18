import Proof.EndpointBoundaryCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The native inverse obeys the canonical coercive inverse estimate before
    any actual coefficient is substituted into its operator argument. -/
theorem norm_nativeZeroFunctionalInverse_le (B : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (α : ℝ) (hα : 0 < α) (hB : ∀ u,α*‖u‖*‖u‖ ≤ B u u) :
    ‖nativeZeroFunctionalInverse B‖ ≤ α⁻¹ := by
  change ‖functionalInverse B‖ ≤ α⁻¹
  exact norm_functionalInverse_le B α hα hB

/-- Coercivity supplies actual invertibility of the weak bilinear operator. -/
theorem isInvertible_of_bilinear_coercive
    (B : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (hc : IsCoercive B) : B.IsInvertible := by
  let I := functionalInverse B
  have hLeft : I.comp B = ContinuousLinearMap.id ℝ BallH1Zero := by
    apply ContinuousLinearMap.ext
    intro u
    exact (eq_functionalInverse B hc (B u) u (fun _ => rfl)).symm
  have hRight : B.comp I = ContinuousLinearMap.id ℝ (StrongDual ℝ BallH1Zero) := by
    apply ContinuousLinearMap.ext
    intro ell
    apply ContinuousLinearMap.ext
    intro v
    exact apply_functionalInverse B hc ell v
  exact ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft

/-- A quantitative raw weak energy lower bound controls the native coefficient
    inverse without repeatedly expanding inherited normed structures. -/
theorem norm_nativeCoefficientWeakFunctionalInverse_le {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (α : ℝ) (hα : 0 < α)
    (hLower : ∀ u : BallH1Zero,α*‖u‖*‖u‖ ≤
      TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ)) (u : BallH1) (u : BallH1)) :
    ‖nativeCoefficientWeakFunctionalInverse a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff‖ ≤ α⁻¹ := by
  change ‖nativeZeroFunctionalInverse (nativeZeroCoefficientEnergyL a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff)‖ ≤ α⁻¹
  apply norm_nativeZeroFunctionalInverse_le _ α hα
  intro u
  exact (hLower u).trans_eq
    ((nativeZeroCoefficientEnergyL_apply a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff u u).trans
      (TauCeti.PDE.energyFormH1L0_apply (mu:=(volume:Measure X)) (Omega:=ballOpens)
        (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff u u)).symm

end ShrinkingSpheres
