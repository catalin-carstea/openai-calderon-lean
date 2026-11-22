module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.Coercivity
public import Proof.CalderonN.GreenRestriction

import Proof.CalderonN.Conformal
import Proof.CalderonN.GreenDilation
import Proof.CalderonN.NormalizedMetric
import Proof.CalderonN.SmoothZonalSobolev
import Proof.CalderonN.WeightedHarmonicConvergence
import Proof.CalderonN.Density
import Proof.CalderonN.SmallJetBounds
import Proof.CalderonN.Bootstrap
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.CompactPointEvaluation
import Proof.CalderonN.EuclideanVolume
import Proof.CalderonN.SourceSobolev
import Proof.CalderonN.FixedBallWeakSource
import Proof.CalderonN.FixedBallMetricEllipticity
import Proof.CalderonN.LocalGreenL2
import Proof.CalderonN.LocalGreenPointwise
import Proof.CalderonN.GreenSourceTesting
import Proof.CalderonN.LowerCrossGreen
import Proof.CalderonN.RescaledProductJets
import Proof.CalderonN.UniformProductCross
import Proof.CalderonN.QuantitativePhaseSweep
import Proof.CalderonN.HarmonicInterpolationChain
import Proof.CalderonN.GlobalChartReduction
import Proof.CalderonN.RemainderAbsorption
import Proof.CalderonN.FixedTube.GreenInitialization
import Proof.CalderonN.FixedTube.SeparatedAgreement
import Proof.CalderonN.MovingSphere.RadiusSeed
import Proof.CalderonN.MovingSphere.FramedEnergy
import Proof.CalderonN.MovingSphere.Smallness
import Proof.CalderonN.ConformalDepth
import Proof.CalderonN.SoftplusComposition
import Proof.CalderonN.RadiusProfileGeometry
import Proof.CalderonN.FrameJetBound
import Proof.CalderonN.ShrinkingRadiusParameter
import Proof.CalderonN.NormalPhase
import Proof.CalderonN.FrameOperators
import Proof.CalderonN.FramedNormalGauss
import Proof.CalderonN.FirstMetricNormalDensity
import Proof.CalderonN.ExpJetBounds
import Proof.CalderonN.PolynomialDriftVariation
import Proof.CalderonN.MovingRadius
import Proof.CalderonN.MetricPullback
import Proof.CalderonN.PrincipalMetric
import Proof.CalderonN.CylinderSeed
import Proof.CalderonN.MovingSphere.Propagation
import Proof.CalderonN.CoordinateJets
import Proof.CalderonN.ProfileCovariant
import Proof.CalderonN.DilationSmallJet
import Proof.CalderonN.NormalCenterBoundaryChainRule
import Proof.CalderonN.FirstMetricNormalJets
import Proof.CalderonN.FramedNormalRadialCoefficient
import Proof.CalderonN.NormalPhaseHessian
import Proof.CalderonN.JacobiInterval
import Proof.CalderonN.ParallelFrameCalculus
import Proof.AdjointCancelledRemainderDerivative
import Proof.CalderonN.ProfileBounds
import Proof.CalderonN.FramedConnectionCorrection
import Proof.CalderonN.ProductFramedStrict
import Proof.CalderonN.NormalBallHarmonic
import Proof.CalderonN.MovingSphere.SeparatedEndpoints
import Proof.CalderonN.MovingSphere.CylinderRadiusSeed
import Proof.CalderonN.FixedBallDirichletUnique
import Proof.CalderonN.NormalTransportedPhase
import Proof.CalderonN.FirstMetricConormal
import Proof.CalderonN.MovingSphere.UniformStrict
import Proof.CalderonN.MovingSphere.GreenContinuation
import Proof.CalderonN.NormalDirichlet
import Proof.CalderonN.NormalGreenTransfer
import Proof.CalderonN.NormalFluxDensity
import Proof.CalderonN.SphereCoercivity
import Proof.CalderonN.BallRegularity.BoundedInverse
import Proof.CalderonN.ConformalCylinderAgreement
import Proof.CalderonN.FirstMetricRelativeRadius

import Proof.CalderonN.MetricBallDirichlet

import Proof.CalderonN.ConformalScaledGreenDataJets

import Proof.CalderonN.ChartTransferAssembly

import Proof.CalderonN.ParametricMetricBallDirichlet

import Proof.CalderonN.ActualGreenTransfer

import Proof.CalderonN.EnlargedNormalInverse

import Proof.CalderonN.BallRegularity.UniformStrongInverse

import Proof.CalderonN.ConformalActualGreenTransfer

import Proof.CalderonN.WeightedGreenHorizontal

import Proof.CalderonN.BundleTraceLinearity

import Proof.CalderonN.TraceResidualBounds

import Proof.CalderonN.ChartActualTransfer
import Proof.CalderonN.ChartNormalization

import Proof.CalderonN.ActualRelativeRadiusPoisson
import Proof.CalderonN.ActualFiniteHarmonicRadialTaylor
import Proof.CalderonN.ActualNormalPoissonIdentification

import Proof.CalderonN.WeakConormalTaylorBound

import Proof.CalderonN.FixedBallWeakEnergyBound

import Proof.CalderonN.ActualFiniteWeakConormalTaylor

import Proof.CalderonN.PolynomialConormalFirstVariation

import Proof.CalderonN.SmoothBoundarySobolev

import Proof.CalderonN.ActualConormalSobolevTaylor

import Proof.CalderonN.ActualConormalRadialRow

import Proof.CalderonN.ActualFiniteWeakRadialTaylor

import Proof.CalderonN.ActualFiniteRadialMidpoint

import Proof.CalderonN.ActualWeakAngularConormal

import Proof.CalderonN.ActualAngularRadialMidpoint

import Proof.CalderonN.ActualMovingVelocityTaylor

import Proof.CalderonN.FiniteAngularDriftModel

import Proof.CalderonN.ActualCenterCoefficientTaylor

import Proof.CalderonN.FiniteLinearizedConormal

import Proof.CalderonN.BallDilationCalculus

import Proof.CalderonN.MovingTraceNormIdentity

import Proof.CalderonN.ActualCenterRadialResponse

import Proof.CalderonN.ActualRelativeRadiusRadialResponse

import Proof.CalderonN.ActualRadialParameterFamilies

import Proof.CalderonN.AdmittedNormalBallPullback

import Proof.CalderonN.AdmittedMovingTraceAdjoint

import Proof.CalderonN.GaussVelocityAdjoint

import Proof.CalderonN.AdmittedGaussRadialAdjoint

import Proof.CalderonN.FinitePhysicalDegreeForm

import Proof.CalderonN.ActualConormalDegreeForm

import Proof.CalderonN.ActualSmoothConormalDegreeForm

import Proof.CalderonN.ActualSmoothConormalMultiplier

import Proof.CalderonN.CoordinateHarmonicRaising

import Proof.CalderonN.ActualAdjointAffineNormalForm

import Proof.CalderonN.ActualHigherConormalDegree

import Proof.CalderonN.MovingTraceBaseCommutators

import Proof.CalderonN.SmoothTraceDualOrder

import Proof.CalderonN.PhysicalEnergyFrameInvariance

import Proof.CalderonN.MovingTracePrincipalDecomposition

import Proof.CalderonN.MovingTraceBaseAdjoints

import Proof.CalderonN.JointNormalCoefficientJets

import Proof.CalderonN.WeightedTraceErrorForm

import Proof.CalderonN.WeightedDegreeSylvester

import Proof.CalderonN.SmoothTraceMultiplierOrder

import Proof.CalderonN.SmoothTraceFiniteExt

import Proof.CalderonN.FlatTraceRaisingIdentities

import Proof.CalderonN.SmoothSupportedTraceAdjoints

import Proof.CalderonN.ActualNormalCoefficientRemainder

import Proof.CalderonN.SmoothSupportedTraceFiberAction

import Proof.CalderonN.BanachInverseFamilyJetBounds

import Proof.CalderonN.PoissonAffineRemainderHigherJets

import Proof.CalderonN.ActualRelativeCoefficientGerms

import Proof.CalderonN.ParameterSpatialJetBounds

import Proof.CalderonN.SmoothSupportedTraceBaseAdjoint

import Proof.CalderonN.SmoothTraceWeightedCasimir

import Proof.CalderonN.SmoothTraceWeightedDegree

import Proof.CalderonN.SmoothTraceMultiplierDegreeComm

import Proof.CalderonN.ActualRelativeStrongOperatorJets

import Proof.CalderonN.FactoredPoissonJetBounds

import Proof.CalderonN.ActualRelativeWeakEnergyGerm

import Proof.CalderonN.BilinearTaylorHigherJets

import Proof.CalderonN.SmoothTraceAngularCommutator

import Proof.CalderonN.ActualTraceSections

import Proof.CalderonN.SmoothTraceRaisingProjection

import Proof.CalderonN.WeakEnergyPoissonJets

import Proof.CalderonN.FlatStrongOperatorInvertible

import Proof.CalderonN.SmoothSupportedTraceHorizontal

import Proof.CalderonN.WeakEnergyConormalJets

import Proof.CalderonN.NormalizedParallelCenterZeroJets

import Proof.CalderonN.PhysicalTraceModelAdjoint

import Proof.CalderonN.ActualNormalizedParallelCenterJets

import Proof.CalderonN.LiftedPoissonTaylorJets

import Proof.CalderonN.WeakEnergyPoissonDifferenceJets

import Proof.CalderonN.ActualFramedCenterVelocityRemainder

import Proof.CalderonN.ActualSupportedTraceNorm

import Proof.CalderonN.PhysicalTraceComparison

import Proof.CalderonN.ActualGaussOperatorExpansion

import Proof.CalderonN.TraceCoordinateModel

import Proof.CalderonN.ActualSupportedAffineRegular

import Proof.CalderonN.PhysicalMovingTraceDecomposition

import Proof.CalderonN.ActualGaussConormalBounds

import Proof.CalderonN.TraceCoordinatePotential

import Proof.CalderonN.MovingTracePerturbationBaseNormal

import Proof.CalderonN.ProfileOrdinaryJetBound

import Proof.CalderonN.UniformBackgroundChristoffelJets

import Proof.CalderonN.FixedBallWeakConormalFamilyJets

import Proof.CalderonN.ScaledRadiusJetBudget

import Proof.CalderonN.SmallPrincipalOrdinaryJets

import Proof.CalderonN.ActualRelativeWeakConormalTaylor

import Proof.CalderonN.FixedBallWeakConormalTraceAgreement

import Proof.CalderonN.ActualMovingTraceBaseNormal

import Proof.CalderonN.ActualPhysicalWeakConormalJets

import Proof.CalderonN.ActualSupportedConormal

import Proof.CalderonN.SupportedSphereMultiplierFamily

import Proof.CalderonN.ActualMovingTraceComparison

import Proof.CalderonN.UniformActualGaussPairedAdjoints

import Proof.CalderonN.WeakConormalRotatedTaylorJets

import Proof.CalderonN.ParametricBallRotationCoefficientJets

import Proof.CalderonN.ActualRelativeRotatedWeakEnergy

import Proof.CalderonN.ActualFiniteRotatedConormalIdentity

import Proof.CalderonN.PhysicalTraceScalarJets

import Proof.CalderonN.ActualSupportedConormalRemainder

import Proof.CalderonN.ActualLowerOrderCancellation

import Proof.CalderonN.PhysicalTraceLowerOrderMass

import Proof.CalderonN.PhysicalConormalMatrixJetBounds

import Proof.CalderonN.SmoothSupportedFiberMatrixDerivative

import Proof.CalderonN.ActualGaussConormalFirstBaseBounds

import Proof.CalderonN.ActualGaussConormalMultiplierBounds

import Proof.CalderonN.SmoothSupportedFiberDerivativeCalculus

import Proof.CalderonN.TraceCoordinateHorizontalRaisingComm

import Proof.CalderonN.SmoothLinearTraceMultiplierBounds

import Proof.CalderonN.UniformMetricInverseEntryJets

import Proof.CalderonN.PhysicalChartAngularJetComposition

import Proof.CalderonN.ActualSupportedLowerOrderVelocity

import Proof.CalderonN.SupportedSphereMultiplierBounds

import Proof.CalderonN.SmoothTraceRotationBracket

import Proof.CalderonN.FlatTraceRaisingBounds

import Proof.CalderonN.PhysicalLowerOrderFiberEstimate

import Proof.CalderonN.UniformTraceCoordinateBounds

import Proof.CalderonN.ActualRadialMultiplierBounds

import Proof.CalderonN.ActualLowerVelocityCoefficientBounds

import Proof.CalderonN.ActualCenterCorrectionGerms

import Proof.CalderonN.UniformActualLowerOrderNorm

import Proof.CalderonN.ActualErrorCoercivityCaller

import Proof.CalderonN.ActualGaussConormalScalarCommutators

import Proof.CalderonN.ActualQuadraticVelocityIdentity

import Proof.CalderonN.ActualGaussConormalHigherBaseBounds

import Proof.CalderonN.MovingTraceFirstOrderForms

import Proof.CalderonN.MovingTraceDriftSplit

import Proof.CalderonN.UniformActualDriftRemainderNorm

import Proof.CalderonN.SmoothSupportedFiberJetBounds

import Proof.CalderonN.SupportedSphereMultiplierHigherDerivatives

import Proof.CalderonN.SmoothTraceSymbolCommutators

import Proof.CalderonN.UniformActualTraceVelocityFactors

import Proof.CalderonN.ActualTraceBackgroundScalarJets

import Proof.CalderonN.ActualTraceDensityScalarJets

import Proof.CalderonN.UniformActualPrincipalTraceError

public section

open Set

namespace CalderonN

/-- Proposition 5.3 for any fixed dimension at least three. -/
theorem coercivity {n : ℕ} (hn : 3 ≤ n) : Coercivity n := by
  letI : NeZero n := ⟨by omega⟩
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  exact coercivity_of_uniformActualMovingTracePrincipalError hn
    (uniform_actualMovingTracePrincipalError hn)

/-- Theorem 3.1 in the common harmonic chart. The ambient Dirichlet
Green kernels are used by their restrictions to the chart. -/
theorem localMetricExtension
    {n : ℕ} (hn : 3 ≤ n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsSmoothSide Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : X n × X n → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {m : ℕ} {u₁ u₂ : Fin m → X n → ℝ}
    (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a)) (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a))
    (hpairs : ∀ a, EqOn (u₁ a) (u₂ a) W) (hspan : HessianSpanning g₁ u₁) :
    ∃ r > 0, Metric.ball (0 : X n) r ⊆ Ω ∧ EqOn g₁ g₂ (Metric.ball 0 r) := by
  letI : NeZero n := ⟨by omega⟩
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  exact localMetricExtension_of_normalized 0
    (normalizedLocalMetricExtension_of_coercivity (normal := 0) hn (coercivity hn))
    hΩ hW hWΩ hside hg₁ hg₂ hchart₁ hchart₂ hG₁ hG₂ hmetric hgreen hu₁ hu₂ hpairs hspan

end CalderonN
