import Proof.NativeEllipticWeakData
import Proof.NativeWeakTaylorOperators
import Proof.CommonSupportLowRadialRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Actual rotated ellipticity supplies both genuine inverses and smoothness
    of the actual low radial family for every angle, without exterior ellipticity. -/
theorem actual_rotated_low_radial_invertibility
    (H : MetricField) (KP : ℝ) (hKP : 1 ≤ KP)
    (hEll : Elliptic (Metric.closedBall (0:X) 2) KP H) (i j : I)
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0)
    (hRep : ∀ θ z,z ∈ (ballOpens:Set X) → a (θ,z) = coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => principalCoefficient H v.2) ((θ,0),z)) :
    (∀ θ,(commonSupportZeroWeakEnergy a ha θ).IsInvertible) ∧
    (∀ θ,(negativeBoundaryCoefficientMulL (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz θ))).IsInvertible) ∧
    ContDiff ℝ ∞ (commonSupportLowRadialErrorL a ha S hS hz) := by
  have hBase := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
  have hWeak (θ : ℝ) : (commonSupportZeroWeakEnergy a ha θ).IsInvertible := by
    have hNative := nativeWeakEnergyData_of_rotated_coefficient H KP hKP hEll i j θ
      (fun z => a (θ,z)) (ha.continuous.comp (continuous_const.prodMk continuous_id)) (hRep θ)
    exact nativeZeroCoefficientEnergy_isInvertible (a:=fun z => a (θ,z)) (commonSupportEnergyMemLp a ha θ) hNative.coercive
  have hNormal (θ : ℝ) :
      (negativeBoundaryCoefficientMulL (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz θ))).IsInvertible := by
    have hRot := uniformlyEllipticOn_unitBall_orthogonal
      (OAI.AnisotropicCalderon.SmoothSphereRotation.coordinateRotationIsometry i j θ)
      (principalCoefficient H) _ _ hBase
    have hActual := hRot.congr (fun z hzB => (hRep θ z hzB).trans
      (coordinateRotationPrincipalFamily_eq_orthogonal i j
        (fun v : ℝ × X => principalCoefficient H v.2) θ 0 z))
    apply negativeNormalCoefficient_isInvertible (commonSupportMatrixFamily 2 a ha S hS hz θ)
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz θ))
      (coefficientSmoothData_normalCoefficientJet _) _ _
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hActual
  refine ⟨hWeak,hNormal,?_⟩
  exact contDiffOn_univ.mp (contDiffOn_commonSupportLowRadialErrorL a ha S hS hz Set.univ
    (fun θ _ => hWeak θ) (fun θ _ => hNormal θ))

end ShrinkingSpheres
