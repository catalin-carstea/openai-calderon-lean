import Proof.HalfMultiplierTaylorPoint
import Proof.FlatAffineCoefficientC1

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

def halfMultiplierTaylorUniformBudget (C P Q q CP1 CP2 : ℝ) : ℝ :=
  let L := 15*nativeMultiplierForcingGradientBudget
  let QA := multiplierInverseTaylorBudget C P Q
  let DA := multiplierInverseDifferenceBudget C P Q
  let H := ‖fixedHarmonicH1LiftL‖
  ‖fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL‖*
    (C*((L*q)*CP2+(L*P+L*Q)*CP1+L*Q*H)+
      (DA+QA)*(L*CP1+L*P*H)+QA*(L*H))

lemma halfMultiplierTaylorUniformBudget_nonneg (C P Q q CP1 CP2 : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hq : 0 ≤ q)
    (hCP1 : 0 ≤ CP1) (hCP2 : 0 ≤ CP2) :
    0 ≤ halfMultiplierTaylorUniformBudget C P Q q CP1 CP2 := by
  have hG := nativeMultiplierForcingGradientBudget_nonneg
  have hS := strongC1OperatorBudget_nonneg fixedSobolevCalculus
  unfold halfMultiplierTaylorUniformBudget multiplierInverseTaylorBudget multiplierInverseDifferenceBudget
  positivity

/-- The point remainder constant is linear in the multiplier jet budget,
with no dependence on the exterior extension or on its coefficient norm. -/
theorem halfMultiplierTaylorPointBudget_le_uniform
    (F0 : SmoothCoefficientMatrix 2) (Qm : SmoothCoefficientJets 3)
    (C P Q q B CP1 CP2 : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hq : 0 ≤ q)
    (hB : 0 ≤ B) (hCP1 : 0 ≤ CP1) (hCP2 : 0 ≤ CP2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Qm) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Qm) w) j) z‖ ≤ B) :
    halfMultiplierTaylorPointBudget F0 Qm C P Q q B CP1 CP2 ≤
      halfMultiplierTaylorUniformBudget C P Q q CP1 CP2*B := by
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Qm
  let L := 15*nativeMultiplierForcingGradientBudget*B
  let QA := multiplierInverseTaylorBudget C P Q
  let DA := multiplierInverseDifferenceBudget C P Q
  have hG := nativeMultiplierForcingGradientBudget_nonneg
  have hS := strongC1OperatorBudget_nonneg fixedSobolevCalculus
  have hL : 0 ≤ L := by dsimp [L];positivity
  have hQA : 0 ≤ QA := by dsimp [QA,multiplierInverseTaylorBudget];positivity
  have hDA : 0 ≤ DA := by dsimp [DA,multiplierInverseDifferenceBudget];positivity
  obtain ⟨hVal0,hDer0⟩ := flat_compact_coefficient_local_jets F0 hFlat
  have hK0 : ‖K0‖ ≤ L := by
    have h := norm_nativeBulkMultiplierForcing_local_C1 F0 Qm 1 B (by norm_num) hB hVal0
      (by intro i j z hz;rw [TauCeti.norm_gradient_eq_norm_fderiv,hDer0 i j z hz,norm_zero];norm_num) hQ1 hQ2
    exact h.trans_eq (by dsimp [L];ring)
  have hK0P : ‖K0.comp fixedHarmonicH1LiftL‖ ≤ L*‖fixedHarmonicH1LiftL‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hK0 (norm_nonneg _))
  change ‖fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL‖*
    (C*((L*q)*CP2+(L*P+L*Q)*CP1+L*Q*‖fixedHarmonicH1LiftL‖)+
      (DA+QA)*(‖K0‖*CP1+L*P*‖fixedHarmonicH1LiftL‖)+QA*‖K0.comp fixedHarmonicH1LiftL‖) ≤ _
  calc
    _ ≤ ‖fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL‖*
      (C*((L*q)*CP2+(L*P+L*Q)*CP1+L*Q*‖fixedHarmonicH1LiftL‖)+
        (DA+QA)*(L*CP1+L*P*‖fixedHarmonicH1LiftL‖)+QA*(L*‖fixedHarmonicH1LiftL‖)) := by gcongr
    _ = _ := by dsimp only [halfMultiplierTaylorUniformBudget,L,QA,DA];ring

end ShrinkingSpheres
