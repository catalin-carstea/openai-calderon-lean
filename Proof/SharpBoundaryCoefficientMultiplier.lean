import Proof.EndpointBoundaryCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeHalfSmoothMultiplier OAI.AnisotropicCalderon.TraceKernel

def boundaryHalfMultiplierBudget : ℝ :=
  2*‖fixedHalfValueTraceL‖*‖fixedHarmonicH1LiftL‖

lemma boundaryHalfMultiplierBudget_nonneg : 0 ≤ boundaryHalfMultiplierBudget := by
  unfold boundaryHalfMultiplierBudget
  positivity

/-- Half-order boundary multiplication requires only local C0/C1 bulk control;
    exterior coefficient jets do not enter the bound. -/
theorem norm_nativeHalfCoefficientMulL_local_C1 (F : SmoothCoefficientJets 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ x ∈ (ballOpens : Set X),|coefficientValue 2 F x| ≤ q)
    (hDerivative : ∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 F) x‖ ≤ q) :
    ‖nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace F‖ ≤ boundaryHalfMultiplierBudget*q := by
  have hG (x : X) (hx : x ∈ (ballOpens : Set X)) :
      ‖gradient (coefficientSmoothData F).1 x‖ ≤ q := by
    change ‖gradient (coefficientValue 2 F) x‖ ≤ q
    rw [norm_gradient_eq_norm_fderiv]
    exact hDerivative x hx
  rw [nativeHalfCoefficientMulL_eq_smoothMulL fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace F hq hValue hG]
  exact (norm_nativeHalfSmoothMulL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    fixedUnitBallValueTrace (coefficientSmoothData F) hq hValue hG).trans_eq
    (by unfold boundaryHalfMultiplierBudget fixedHalfValueTraceL fixedHarmonicH1LiftL;ring)

/-- Duality gives the identical local C1 bound at the negative half endpoint. -/
theorem norm_nativeNegativeHalfCoefficientMulL_local_C1 (F : SmoothCoefficientJets 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ x ∈ (ballOpens : Set X),|coefficientValue 2 F x| ≤ q)
    (hDerivative : ∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 F) x‖ ≤ q) :
    ‖nativeNegativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace F‖ ≤ boundaryHalfMultiplierBudget*q := by
  have hAdj : ‖nativeNegativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics fixedUnitBallValueTrace F‖ =
      ‖nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace F‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  exact hAdj.le.trans (norm_nativeHalfCoefficientMulL_local_C1 F q hq hValue hDerivative)

end ShrinkingSpheres
