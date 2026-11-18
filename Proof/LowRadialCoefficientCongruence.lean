import Proof.NativeWeakCoefficientCongruence
import Proof.CommonSupportRadialTaylorIdentity
import Proof.ConormalSymmetry
import Proof.UniformLowRadialTaylor
import Proof.RadialConormalReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies

/-- The actual low radial operator is independent of exterior coefficient
    representatives, by equality on the physical ball and boundary sphere. -/
theorem actualLowRadialError_congr_coefficients {a b : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb : MemLp (fun z => TauCeti.PDE.energyIntegrand (b z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (F G : SmoothCoefficientMatrix 2)
    (hBall : ∀ z ∈ (ballOpens:Set X),a z = b z)
    (hSphere : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = coefficientMatrixField 2 G w.val) :
    actualLowRadialErrorL a ha F = actualLowRadialErrorL b hb G := by
  have hN := nativeWeakConormal_congr_unitBall ha hb hBall
  change nativeWeakConormalEndpoint a (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) ha sphereFischerInner =
    nativeWeakConormalEndpoint b (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) hb sphereFischerInner at hN
  have hM := negativeBoundaryCoefficientMulL_congr_sphere (normalCoefficientJet F) (normalCoefficientJet G)
    (normalCoefficientJet_value_congr_sphere F G hSphere)
  have hT : (fun j => negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)) =
      fun j => negativeBoundaryCoefficientMulL (tangentCoefficientJet G j) := by
    funext j
    exact negativeBoundaryCoefficientMulL_congr_sphere _ _ (tangentCoefficientJet_value_congr_sphere F G hSphere j)
  unfold actualLowRadialErrorL
  rw [hN,hM,hT]

/-- The genuine first correction chosen by the angle family equals every
    same-coefficient first correction used in the checked point Taylor bound. -/
theorem commonSupport_lowFirstRadial_eq_of_coefficient
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1) (S1 : Set X) (hS1 : IsCompact S1)
    (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0) (p : P) (c : ℝ) (F1 : SmoothCoefficientMatrix 2)
    (hF1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hPoint : ∀ z ∈ Metric.closedBall (0:X) 2,a1 (p,z) = coefficientMatrixField 2 F1 z) :
    commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c p = lowFirstRadialVariationL c F1 hF1 := by
  have hN := weakFirstConormal_congr_on_ball c (commonSupportEnergyMemLp a1 ha1 p) hF1
    (fun z hzB => hPoint z (unitBall_subset_closedBall_two hzB))
  have hSphere (w : UnitSphere) : coefficientMatrixField 2 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 p) w.val =
      coefficientMatrixField 2 F1 w.val := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hPoint w.val (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property))
  have hM := negativeBoundaryCoefficientMulL_congr_sphere _ _
    (normalCoefficientJet_value_congr_sphere _ _ hSphere)
  unfold commonSupportLowFirstRadialL lowFirstRadialVariationL
  rw [hN,commonSupport_negative_normal_multiplier_eq,hM]

end ShrinkingSpheres
