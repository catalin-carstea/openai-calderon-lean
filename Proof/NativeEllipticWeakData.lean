import Proof.NativeWeakEnergyData
import Proof.OrthogonalEllipticity
import Proof.Archive.CoordinateRotationCoefficientFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Genuine local ellipticity gives quantitative native weak inverse data
    without imposing any condition on the coefficient outside the ball. -/
theorem nativeWeakEnergyData_of_uniformlyElliptic {a : X → Mat} {lam Lam : ℝ}
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) a lam Lam)
    (hMeas : AEStronglyMeasurable a ((volume:Measure X).restrict ballOpens)) :
    NativeWeakEnergyData a (5*lam⁻¹) Lam := by
  let hcoeff := memLp_zeroDriftEnergyIntegrand hUE hMeas
  refine ⟨hcoeff,isCoercive_unitBall_zeroDrift hUE hMeas hcoeff,?_,?_⟩
  · have hAlpha : 0 < lam/5 := div_pos hUE.pos (by norm_num)
    have hLower (u : BallH1Zero) : (lam/5)*‖u‖*‖u‖ ≤
        TauCeti.PDE.energyFormH1 a 0 0 (u:BallH1) (u:BallH1) :=
      (unitBall_zeroDrift_coercivity hUE hMeas hcoeff u).trans_eq
        (TauCeti.PDE.energyFormH1L0_apply hcoeff u u)
    have hN := norm_nativeCoefficientWeakFunctionalInverse_le hcoeff (lam/5) hAlpha hLower
    exact hN.trans_eq (by simp only [div_eq_mul_inv,mul_inv_rev,inv_inv])
  · have hN := TauCeti.PDE.norm_energyFormH1L_le_of_bounds (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) (Lam:=Lam) (beta:=0) (gamma:=0)
      hcoeff hUE.upper_nonneg (fun x hx => hUE.upper_bound hx) le_rfl le_rfl
      (fun _ _ => by simp) (fun _ _ => by simp)
    simpa only [add_zero] using hN

/-- Rotating the actual geometric coefficient preserves its true weak
    coercivity and inverse constants for every smooth agreeing representative. -/
theorem nativeWeakEnergyData_of_rotated_coefficient
    (H : MetricField) (KP : ℝ) (hKP : 1 ≤ KP)
    (hEll : Elliptic (Metric.closedBall (0:X) 2) KP H)
    (i j : I) (θ : ℝ) (a : X → Mat) (ha : Continuous a)
    (hField : ∀ z ∈ (ballOpens:Set X),a z = coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => principalCoefficient H v.2) ((θ,0),z)) :
    NativeWeakEnergyData a (5*metricDensityBudget KP*KP) (metricDensityBudget KP*KP) := by
  have hUE := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
  have hRot := uniformlyEllipticOn_unitBall_orthogonal
    (OAI.AnisotropicCalderon.SmoothSphereRotation.coordinateRotationIsometry i j θ)
    (principalCoefficient H) _ _ hUE
  have hActual := hRot.congr (fun z hz => (hField z hz).trans
    (coordinateRotationPrincipalFamily_eq_orthogonal i j
      (fun v : ℝ × X => principalCoefficient H v.2) θ 0 z))
  have hMeas : AEStronglyMeasurable a ((volume:Measure X).restrict ballOpens) := ha.aestronglyMeasurable
  have hData := nativeWeakEnergyData_of_uniformlyElliptic hActual hMeas
  simpa only [mul_inv_rev,inv_inv,mul_assoc,mul_comm,mul_left_comm] using hData

end ShrinkingSpheres
