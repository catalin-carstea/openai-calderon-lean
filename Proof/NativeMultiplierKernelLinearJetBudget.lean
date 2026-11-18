import Proof.MultiplierKernelTaylorScalarBudget
import Proof.CommonSupportNativeMultiplierKernelHigherJets
import Proof.NativeMultiplierForcingBilinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def nativeMultiplierKernelLinearJetBudget (N : ℕ) (F0 : SmoothCoefficientMatrix 2)
    (CI C0 CW CW0 qA P1 QR : ℝ) : ℝ :=
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let CA1 := 2*SB*P1
  let CG := 270*nativeMultiplierForcingGradientBudget
  let CQI := |strongInverseTaylorJetBudget N CI C0 qA P1 QR|
  multiplierKernelTaylorScalarJetBudget (V:=BallSobolev 0) N
    (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
    (15*nativeMultiplierForcingGradientBudget*‖F0‖)
    (inverseFamilyJetBudget N CI (2*SB*qA)) C0 CA1 (CG*qA) (C0*C0*CA1+CQI) CQI
    (CG*QR) (CG*P1) |weakPoissonTaylorJetBudget N CW CW0 qA P1 QR|
    (CW0*(weakFullDerivativeBudget*P1)*‖fixedHarmonicH1LiftL‖)

/-- The checked fixed-multiplier budget is uniformly linear in its norm.
    The flat coefficient representative is chosen before the admitted data. -/
theorem nativeMultiplierKernelTaylorJetBudget_le_linear
    (N : ℕ) (F0 : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3)
    (CI C0 CW CW0 qA P1 QR : ℝ)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hCW0 : 0 ≤ CW0) (hqA : 0 ≤ qA) (hP1 : 0 ≤ P1) :
    nativeMultiplierKernelTaylorJetBudget N F0 Q CI C0 CW CW0 qA P1 QR ‖Q‖ ≤
      nativeMultiplierKernelLinearJetBudget N F0 CI C0 CW CW0 qA P1 QR*‖Q‖ := by
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let CA1 := 2*SB*P1
  let CG := 270*nativeMultiplierForcingGradientBudget*‖Q‖
  let CQI := |strongInverseTaylorJetBudget N CI C0 qA P1 QR|
  let CIJ := inverseFamilyJetBudget N CI (2*SB*qA)
  let CP1 := CW0*(weakFullDerivativeBudget*P1)*‖fixedHarmonicH1LiftL‖
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
  let L0 := 15*nativeMultiplierForcingGradientBudget*‖F0‖
  have hSB : 0 ≤ SB := strongC1OperatorBudget_nonneg _
  have hWB := weakFullDerivativeBudget_nonneg
  have hCA1 : 0 ≤ CA1 := by dsimp only [CA1];positivity
  have hCIJ : 0 ≤ CIJ := inverseFamilyJetBudget_nonneg N CI (2*SB*qA) hCI (by positivity)
  have hCP1 : 0 ≤ CP1 := by dsimp only [CP1];positivity
  have hK0 : ‖K0‖ ≤ L0*‖Q‖ := norm_nativeBulkMultiplierForcing_matrix_multiplier_le F0 Q
  have hBound := multiplierKernelTaylorJetBudget_le_scalar N
    (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL K0
    (L0*‖Q‖) CIJ C0 CA1 (CG*qA) (C0*C0*CA1+CQI) CQI (CG*QR) (CG*P1)
    |weakPoissonTaylorJetBudget N CW CW0 qA P1 QR| CP1 hK0 hCIJ hC0 hCA1 (abs_nonneg _) hCP1
  exact hBound.trans_eq (by
    dsimp only [nativeMultiplierKernelLinearJetBudget,multiplierKernelTaylorScalarJetBudget,
      SB,CA1,CG,CQI,CIJ,CP1,K0,L0]
    ring)

end ShrinkingSpheres
