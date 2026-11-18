import Proof.ActualRadialTaylorEndpointCompatibility
import Proof.FlatCoefficientEllipticity
import Proof.NativeEllipticWeakData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Actual rotated ellipticity and exact coefficient agreement supply every
    weak, flat and normal premise of the true Taylor endpoint compatibility. -/
theorem rotated_radial_taylor_endpoints_compatible
    (H : MetricField) (KP : ℝ) (hKP : 1 ≤ KP)
    (hEll : Elliptic (Metric.closedBall (0:X) 2) KP H) (i j : I)
    (a a1 : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0)
    (θ c r : ℝ) (ell : X →L[ℝ] ℝ) (hc : 0 < c) (F0 FH F1H : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hA : ∀ z ∈ Metric.closedBall (0:X) 2,a (θ,z) = coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => principalCoefficient H v.2) ((θ,0),z))
    (hA1 : ∀ z ∈ Metric.closedBall (0:X) 2,a1 (θ,z) = ell (coordinateRotation i j θ z) • (1:Mat))
    (hFH : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 FH z = coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => principalCoefficient H v.2) ((θ,0),z))
    (hF1H : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F1H z = ell (coordinateRotation i j θ z) • (1:Mat))
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 FH).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (actualHighRadialErrorL FH-r • highFirstRadialVariationL F0 F1H c) =
      (commonSupportLowRadialErrorL a ha S hS hz θ-
        r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hNative := nativeWeakEnergyData_of_rotated_coefficient H KP hKP hEll i j θ
    (fun z => a (θ,z)) (ha.continuous.comp (continuous_const.prodMk continuous_id))
    (fun z hzB => hA z (unitBall_subset_closedBall_two hzB))
  have hFirstAE : (fun z => TauCeti.PDE.energyIntegrand (a1 (θ,z)) 0 0) =ᵐ[(volume:Measure X).restrict ballOpens]
      fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1H z) 0 0 := by
    filter_upwards [ae_restrict_mem (ballOpens.isOpen.measurableSet)] with z hzB
    rw [hA1 z (unitBall_subset_closedBall_two hzB),hF1H z (unitBall_subset_closedBall_two hzB)]
  have hFirstMem : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1H z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) := (memLp_congr_ae hFirstAE).mp (commonSupportEnergyMemLp a1 ha1 θ)
  have hFlat := uniformlyEllipticOn_flat_coefficientMatrix F0 c hc hF0
  have hInv0 := strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0 (c • F0) hFlat
  have hBase := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
  have hRot := uniformlyEllipticOn_unitBall_orthogonal (coordinateRotationIsometry i j θ)
    (principalCoefficient H) _ _ hBase
  have hActualUE := hRot.congr (fun z hzB => (hFH z (unitBall_subset_closedBall_two hzB)).trans
    (coordinateRotationPrincipalFamily_eq_orthogonal i j
      (fun v : ℝ × X => principalCoefficient H v.2) θ 0 z))
  have hNormal := negativeNormalCoefficient_isInvertible FH (normalCoefficientJet FH)
    (coefficientSmoothData_normalCoefficientJet FH) _ _ hActualUE
  exact actual_radial_taylor_endpoints_compatible a a1 ha ha1 S S1 hS hS1 hz hz1 θ c r F0 FH F1H
    (fun z => ell (coordinateRotation i j θ z)) hc hNative.coercive hFirstMem hF0
    (fun z hzB => (hFH z hzB).trans (hA z hzB).symm)
    (fun z hzB => (hF1H z hzB).trans (hA1 z hzB).symm)
    (fun w => hA1 w.val (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property))) hInv hInv0 hNormal

end ShrinkingSpheres
