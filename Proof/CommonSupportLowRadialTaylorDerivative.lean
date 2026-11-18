import Proof.LocalLowRadialTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The actual native conormal, normal/tangent and first-variation bounds
    give a quadratic derivative of the same actual low radial Taylor remainder. -/
theorem norm_commonSupportLowRadial_first_remainder_derivative_le
    (a a1 : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0)
    (c r C0 CP CD : ℝ) (hc : c ≠ 0) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hC0 : 0 ≤ C0) (hCP : 0 ≤ CP) (hCD : 0 ≤ CD) (hci : |c⁻¹| ≤ C0)
    (hWeak : ∀ θ,(commonSupportZeroWeakEnergy a ha θ).IsInvertible)
    (hNormal : ∀ θ,(negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz θ))).IsInvertible)
    (hMINorm : ‖(negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz 0)).inverse‖ ≤ CP)
    (hMDiff : ‖negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz 0)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ CP*r)
    (hBPoint : ‖commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c 0‖ ≤ CP)
    (hJPoint : ‖commonSupportLowRadialErrorL a ha S hS hz 0-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c 0‖ ≤ CP*r^2)
    (hDN : ‖fderiv ℝ (fun θ => commonSupportWeakConormalEndpoint a ha θ-c • fixedLowRadialL-
      r • weakFirstConormalVariationL c (fun z => a1 (θ,z)) (commonSupportEnergyMemLp a1 ha1 θ)) 0‖ ≤ CD*r^2)
    (hDM1 : ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 θ)) 0‖ ≤ CD)
    (hDMQ : ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
      r • negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 θ)) 0‖ ≤ CD*r^2)
    (hDT : ∀ j : I,‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j θ)) 0‖ ≤ CD*r^2)
    (hDM : ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)) 0‖ ≤ CD*r)
    (hDE1 : ‖fderiv ℝ (commonSupportFullWeakEnergy a1 ha1) 0‖ ≤ CD) :
    DifferentiableAt ℝ (fun θ => commonSupportLowRadialErrorL a ha S hS hz θ-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ) 0 ∧
    ‖fderiv ℝ (fun θ => commonSupportLowRadialErrorL a ha S hS hz θ-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ) 0‖ ≤
        lowRadialAngleDerivativeBudget C0 CP CD*r^2 := by
  exact norm_commonSupportLowRadial_first_remainder_derivative_le_local a a1 ha ha1 S S1 hS hS1 hz hz1
    c r C0 CP CD (0:ℝ) Set.univ isOpen_univ (mem_univ _) hc hr hr1 hC0 hCP hCD hci
    (fun θ _ => hWeak θ) (fun θ _ => hNormal θ) hMINorm hMDiff hBPoint hJPoint
    hDN hDM1 hDMQ hDT hDM hDE1

end ShrinkingSpheres
