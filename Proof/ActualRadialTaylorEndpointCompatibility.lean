import Proof.RadialTaylorCompatibility
import Proof.LowRadialCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Different actual compact witnesses for the low/high endpoints give the
    same compatible quadratic radial Taylor remainder, including its true first model. -/
theorem actual_radial_taylor_endpoints_compatible
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0)
    (θ : P) (c r : ℝ) (F0 FH F1H : SmoothCoefficientMatrix 2) (s : X → ℝ)
    (hc : 0 < c)
    (hCoercive : IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha θ)))
    (hFirstMem : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1H z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hF0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hField : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 FH z = a (θ,z))
    (hField1 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F1H z = a1 (θ,z))
    (hScalar : ∀ w : UnitSphere,a1 (θ,w.val) = s w.val • (1:Mat))
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 FH).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJet FH)).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (actualHighRadialErrorL FH-r • highFirstRadialVariationL F0 F1H c) =
      (commonSupportLowRadialErrorL a ha S hS hz θ-
        r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz θ
  have hSphere (w : UnitSphere) : coefficientMatrixField 2 F w.val = coefficientMatrixField 2 FH w.val := by
    have hw : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property)
    change coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha S hS hz θ) w.val = _
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact (hField w.val hw).symm
  have hLowEq : commonSupportLowRadialErrorL a ha S hS hz θ =
      actualLowRadialErrorL (fun z => a (θ,z)) (commonSupportEnergyMemLp a ha θ) FH :=
    actualLowRadialError_congr_coefficients (commonSupportEnergyMemLp a ha θ) (commonSupportEnergyMemLp a ha θ)
      F FH (fun _ _ => rfl) hSphere
  have hFirstEq := commonSupport_lowFirstRadial_eq_of_coefficient a1 ha1 S1 hS1 hz1 θ c F1H hFirstMem
    (fun z hzB => (hField1 z hzB).symm)
  have hScalarH (w : UnitSphere) : coefficientMatrixField 2 F1H w.val = s w.val • (1:Mat) :=
    (hField1 w.val (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property))).trans (hScalar w)
  have hCanonical := radial_taylor_endpoints_compatible (commonSupportEnergyMemLp a ha θ) hCoercive
    F0 FH F1H c r s hc hFirstMem
    (fun z hzB => hField z (unitBall_subset_closedBall_two hzB)) hF0 hScalarH hInv hInv0 hNormal
  rw [hLowEq,hFirstEq]
  exact hCanonical

end ShrinkingSpheres
