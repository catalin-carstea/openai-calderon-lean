import Proof.NormalFrameMovingMultiplierCovariant
import Proof.NormalFrameOperatorJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] NormalFrameMultiplierGainFamily.gain NormalFrameMultiplierGainFamily.gainInMultiplier
  radialTaylorMultiplierInMultiplierL radialTaylorMultiplierCommutatorL nativeBulkMultiplierForcingInMultiplierL

/-- The natural point, rotation and covariant budgets of a moving scalar
multiplier in its actual native jet norm. -/
structure NormalFrameMultiplierJetBounds (d : Data) (y : X)
    (q : NormalFrameParameter → SmoothCoefficientJets 3) (B : ℝ) : Prop where
  point : ‖q (y,(d.radius y,frameVectorLinear d.frame y))‖ ≤ B
  rotation : ∀ i j : I,‖deriv (fun t => q (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤ B
  covariant : ∀ a : X,
    ‖deriv (fun t => q (normalFrameActualCurve d.frame d.radius y a t)) 0-
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        deriv (fun t => q (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤
      B*beta d.γ d.radius y*‖a‖

/-- Quantitative moving-multiplier jets follow from the checked fixed-Q
jets and the actual multiplier jets. Both derivative contributions retain
the quadratic radius gain and the multiplier budget remains linear. -/
theorem NormalFrameMultiplierGainFamily.moving_gain_jet_bounds
    {d : Data} {y : X} {A : NormalFrameParameter × X → Mat} {hA : ContDiff ℝ ∞ A}
    {S : Set X} {hS : IsCompact S} {hz : ∀ p z,z ∉ S → A (p,z) = 0}
    {F0 : SmoothCoefficientMatrix 2}
    {ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)} {V : Set NormalFrameParameter}
    (T : NormalFrameMultiplierGainFamily d A hA S hS hz F0 ha0 (d.radius y) V
      (y,(d.radius y,frameVectorLinear d.frame y)))
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p)))
    (hr : DifferentiableAt ℝ d.radius y) (he : DifferentiableAt ℝ (frameVectorLinear d.frame) y)
    (hBeta : 0 ≤ beta d.γ d.radius y)
    (C0 CC CD : ℝ) (hC0 : 0 ≤ C0) (hCC : 0 ≤ CC) (hCD : 0 ≤ CD)
    (hFixed : ∀ Q : SmoothCoefficientJets 3,NormalFrameOperatorJetBounds d y (T.gain Q) ‖Q‖ C0 CC CD)
    (q : NormalFrameParameter → SmoothCoefficientJets 3)
    (hq : DifferentiableAt ℝ q (y,(d.radius y,frameVectorLinear d.frame y)))
    (B : ℝ) (hB : 0 ≤ B) (hQ : NormalFrameMultiplierJetBounds d y q B) :
    NormalFrameOperatorJetBounds d y (fun p => T.gain (q p) p) B C0 (CC+C0) (CD+C0) := by
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  constructor
  · exact (hFixed (q p0)).point.trans (by gcongr;exact hQ.point)
  · intro i j
    have hEq := T.deriv_gain_moving_multiplier_curve hStrong hCoercive
      (normalFrameRotationCurve d.frame d.radius y i j) _
      (hasDerivAt_normalFrameRotationCurve d.frame d.radius y i j)
      (normalFrameRotationCurve_zero d.frame d.radius y i j) q hq
    have hN := (congrArg norm hEq).le.trans (norm_add_le _ _)
    have hA := (hFixed (q p0)).rotation i j
    have hP := (hFixed (deriv (fun t => q (normalFrameRotationCurve d.frame d.radius y i j t)) 0)).point
    have hAB : ‖deriv (fun t => T.gain (q p0) (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤ CC*B*(d.radius y)^2 :=
      hA.trans (by gcongr;exact hQ.point)
    have hPB : ‖T.gain (deriv (fun t => q (normalFrameRotationCurve d.frame d.radius y i j t)) 0) p0‖ ≤ C0*B*(d.radius y)^2 :=
      hP.trans (by gcongr;exact hQ.rotation i j)
    exact hN.trans ((add_le_add hAB hPB).trans_eq (by ring))
  · intro a
    have hEq := T.covariant_moving_multiplier_identity hStrong hCoercive hr he q hq a
    have hN := (congrArg norm hEq).le.trans (norm_add_le _ _)
    let qCov := deriv (fun t => q (normalFrameActualCurve d.frame d.radius y a t)) 0-
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        deriv (fun t => q (normalFrameRotationCurve d.frame d.radius y i j t)) 0
    have hA := (hFixed (q p0)).covariant a
    have hP := (hFixed qCov).point
    have hAB : ‖deriv (fun t => T.gain (q p0) (normalFrameActualCurve d.frame d.radius y a t)) 0-
        ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
          deriv (fun t => T.gain (q p0) (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤
        CD*B*(d.radius y)^2*beta d.γ d.radius y*‖a‖ := hA.trans (by gcongr;exact hQ.point)
    have hPB : ‖T.gain qCov p0‖ ≤ C0*(B*beta d.γ d.radius y*‖a‖)*(d.radius y)^2 :=
      hP.trans (by gcongr;exact hQ.covariant a)
    exact hN.trans ((add_le_add hAB hPB).trans_eq (by ring))

end ShrinkingSpheres
