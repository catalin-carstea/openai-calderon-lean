import Proof.Archive.NativeSmoothMultiplierForcingCoefficients
import Proof.ClosedLocalZeroMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The native bulk H1 product uses only the coefficient's true local C1
size; exterior cutoff jets do not enter the estimate. -/
theorem norm_nativeCoefficientH1ProductL_local_C1 (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),|coefficientValue 2 F z| ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),‖gradient (coefficientValue 2 F) z‖ ≤ q) :
    ‖nativeCoefficientH1ProductL hcalc F‖ ≤ 2*q := by
  have hEq : nativeCoefficientH1ProductL hcalc F = TauCeti.W1p.contDiffSMulL
      (coefficientSmoothData F).1 (coefficientSmoothData F).2 hq h0 h1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact nativeCoefficientH1ProductL_eq_contDiffSMulL hcalc F hq h0 h1 u
  rw [hEq]
  exact TauCeti.W1p.norm_contDiffSMulL_le (coefficientSmoothData F).2 hq h0 h1

def nativeMultiplierForcingGradientBudget : ℝ := ∑ i : I,‖unitBallCoordinateGradientL i‖

lemma nativeMultiplierForcingGradientBudget_nonneg : 0 ≤ nativeMultiplierForcingGradientBudget := by
  unfold nativeMultiplierForcingGradientBudget
  positivity

/-- A local C1/L-infinity forcing bound for the exact supplied multiplier
commutator, retaining its actual column, row and drift coefficients. -/
theorem norm_nativeSmoothMultiplierForcingL_local_C1 (hcalc : FixedSobolevCalculus)
    (C : I → SmoothCoefficientJets 2) (R : I → SmoothCoefficientJets 1) (d : SmoothCoefficientJets 1)
    (P Q D : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (hC0 : ∀ i,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (C i) z| ≤ P)
    (hC1 : ∀ i,∀ z ∈ (ballOpens:Set X),‖gradient (coefficientValue 2 (C i)) z‖ ≤ P)
    (hR : ∀ i,∀ z ∈ (ballOpens:Set X),|coefficientValue 1 (R i) z| ≤ Q)
    (hd : ∀ z ∈ (ballOpens:Set X),|coefficientValue 1 d z| ≤ D) :
    ‖nativeSmoothMultiplierForcingL hcalc C R d‖ ≤ (2*P+Q)*nativeMultiplierForcingGradientBudget+
      D*‖TauCeti.W1p.valueL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2)‖ := by
  let A := ∑ i : I,(unitBallCoordinateGradientL i).comp (nativeCoefficientH1ProductL hcalc (C i))
  let B := ∑ j : I,(coefficientMultiplier hcalc 0 (R j)).comp (unitBallCoordinateGradientL j)
  let V := TauCeti.W1p.valueL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2)
  let E := (coefficientMultiplier hcalc 0 d).comp V
  have hA : ‖A‖ ≤ nativeMultiplierForcingGradientBudget*(2*P) := by
    calc
      _ ≤ ∑ i : I,‖(unitBallCoordinateGradientL i).comp (nativeCoefficientH1ProductL hcalc (C i))‖ := norm_sum_le _ _
      _ ≤ ∑ i : I,‖unitBallCoordinateGradientL i‖*(2*P) := Finset.sum_le_sum (fun i _ =>
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (norm_nativeCoefficientH1ProductL_local_C1 hcalc (C i) P hP (hC0 i) (hC1 i)) (norm_nonneg _)))
      _ = _ := by rw [← Finset.sum_mul];rfl
  have hB : ‖B‖ ≤ Q*nativeMultiplierForcingGradientBudget := by
    calc
      _ ≤ ∑ j : I,‖(coefficientMultiplier hcalc 0 (R j)).comp (unitBallCoordinateGradientL j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : I,Q*‖unitBallCoordinateGradientL j‖ := Finset.sum_le_sum (fun j _ =>
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_coefficientMultiplier_zero_le hcalc (R j) Q hQ (hR j)) (norm_nonneg _)))
      _ = _ := by rw [← Finset.mul_sum];rfl
  have hE : ‖E‖ ≤ D*‖V‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_coefficientMultiplier_zero_le hcalc d D hD hd) (norm_nonneg _))
  change ‖A+B-E‖ ≤ _
  exact ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hA hB) hE).trans_eq (by ring))

end ShrinkingSpheres
