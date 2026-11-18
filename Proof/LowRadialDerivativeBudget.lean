import Proof.CommonSupportRadialTaylorIdentity
import Proof.LowRadialTaylorDerivative

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

def lowRadialAngleDerivativeBudget (C0 CP CD : ℝ) : ℝ :=
  let DB := C0*(sphereSurfaceMass⁻¹*‖fixedHarmonicH1LiftL‖^2*CD+CD*‖fixedLowRadialL‖)
  CP*(CD+CD*‖fixedLowRadialL‖+CD*∑ j : I,‖fixedSphereTangentialL j‖+CD*CP+CP*DB+CD*CP)

lemma lowRadialAngleDerivativeBudget_nonneg (C0 CP CD : ℝ)
    (hC0 : 0 ≤ C0) (hCP : 0 ≤ CP) (hCD : 0 ≤ CD) :
    0 ≤ lowRadialAngleDerivativeBudget C0 CP CD := by
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  unfold lowRadialAngleDerivativeBudget
  positivity


end ShrinkingSpheres
