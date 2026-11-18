import Proof.NormalizedFirstCoefficientTaylor
import Proof.PositiveCoefficientScaling
import Proof.OrderOneBoundaryCoefficient
import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Ellipticity of the genuine normalized coefficient, for every compact
    representative that agrees on the physical unit ball. -/
theorem normalized_coefficient_uniformlyElliptic (d : Data) (y : X)
    (F : SmoothCoefficientMatrix 2) (KP : ℝ) (hKP : 1 ≤ KP)
    (hEll : Elliptic (Metric.closedBall (0:X) 2) KP
      (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)))
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = normalizedFirstNormalCoefficient d y z) :
    TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (coefficientMatrixField 2 F)
      ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*((metricDensityBudget KP)⁻¹*KP⁻¹))
      ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*(metricDensityBudget KP*KP)) := by
  have hActual := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
  have hScaled := uniformlyEllipticOn_positive_const_smul hActual
    (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))
  exact hScaled.congr hField

/-- Normalized actual coefficients remain symmetric and give a positive
    sphere normal multiplier. The native H1 multiplier is therefore invertible. -/
theorem normalized_coefficient_boundary_data (d : Data) (y : X)
    (F : SmoothCoefficientMatrix 2) (KP : ℝ) (hKP : 1 ≤ KP)
    (hEll : Elliptic (Metric.closedBall (0:X) 2) KP
      (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)))
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = normalizedFirstNormalCoefficient d y z) :
    (∀ w : UnitSphere,0 < coefficientValue 2 (normalCoefficientJet F) w.val) ∧
    (oneBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible ∧
    ∀ᵐ z ∂((volume:Measure X).restrict ballOpens),(coefficientMatrixField 2 F z).IsSymm := by
  have hUE := normalized_coefficient_uniformlyElliptic d y F KP hKP hEll hField
  have hPos (w : UnitSphere) : 0 < coefficientValue 2 (normalCoefficientJet F) w.val := by
    rw [coefficientValue_normalCoefficientJet]
    exact boundaryNormalCoefficientData_pos F _ _ hUE w
  refine ⟨hPos,oneBoundaryCoefficientMulL_isInvertible_of_pos _ hPos,?_⟩
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with z hz
  rw [hField z hz]
  change ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹ •
    (OAI.AnisotropicCalderon.vol _ z •
      ((framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z)⁻¹)).IsSymm
  have hSym : ((framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z).IsSymm :=
    (hEll.2 z (unitBall_subset_closedBall_two hz)).1
  exact (hSym.inv.smul _).smul _

end ShrinkingSpheres
