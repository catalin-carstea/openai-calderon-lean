import Proof.NativeBulkMultiplierForcingBound
import Proof.CoefficientOperatorLocality

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

lemma coefficientMultiplier_affine_on_ball (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F F0 F1 : SmoothCoefficientJets (k+1)) (r : ℝ)
    (h : ∀ z ∈ (ballOpens:Set X),coefficientValue (k+1) F z =
      coefficientValue (k+1) F0 z+r*coefficientValue (k+1) F1 z) :
    coefficientMultiplier hcalc k F = coefficientMultiplier hcalc k F0+r • coefficientMultiplier hcalc k F1 := by
  have hEq := coefficientMultiplier_congr_on_ball hcalc k F (F0+r • F1) (by
    intro z hz
    simpa only [coefficientValue_add,coefficientValue_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using h z hz)
  exact hEq.trans (by rw [coefficientMultiplier_add,coefficientMultiplier_smul])

lemma nativeCoefficientH1ProductL_affine_on_ball (hcalc : FixedSobolevCalculus)
    (F F0 F1 : SmoothCoefficientJets 2) (r : ℝ)
    (h : ∀ z ∈ (ballOpens:Set X),coefficientValue 2 F z = coefficientValue 2 F0 z+r*coefficientValue 2 F1 z) :
    nativeCoefficientH1ProductL hcalc F = nativeCoefficientH1ProductL hcalc F0+r • nativeCoefficientH1ProductL hcalc F1 := by
  unfold nativeCoefficientH1ProductL
  rw [coefficientMultiplier_affine_on_ball hcalc 1 F F0 F1 r h,
    ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul]

lemma nativeBulkMultiplierForcing_zero_drift (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) :
    nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q =
      (∑ i : I,(unitBallCoordinateGradientL i).comp
        (nativeCoefficientH1ProductL hcalc (smoothMultiplierColumnJets F Q i)))+
      (∑ j : I,(coefficientMultiplier hcalc 0 (smoothMultiplierRowJets F Q j)).comp
        (unitBallCoordinateGradientL j)) := by
  have hd : coefficientMultiplier hcalc 0 (smoothMultiplierDriftJets (fun _ : I => (0:SmoothCoefficientJets 1)) Q) = 0 := by
    have hEq := coefficientMultiplier_congr_on_ball hcalc 0
      (smoothMultiplierDriftJets (fun _ : I => (0:SmoothCoefficientJets 1)) Q) 0 (by
        intro z hz
        rw [coefficientValue_smoothMultiplierDriftJets]
        change (∑ i : I,(0:ℝ)*(gradient (coefficientValue 3 Q) z) i) = 0
        simp)
    exact hEq.trans ((coefficientMultiplierL hcalc 0).map_zero)
  simp only [nativeBulkMultiplierCommutatorForcingL,nativeSmoothMultiplierForcingL,hd,
    ContinuousLinearMap.zero_comp,sub_zero]

/-- Exact affine coefficient agreement on the physical ball gives exact
    affine agreement of the SAME order-one bulk multiplier forcing. -/
theorem nativeBulkMultiplierForcing_affine_on_ball (hcalc : FixedSobolevCalculus)
    (F F0 F1 : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) (r : ℝ)
    (h : ∀ z ∈ (ballOpens:Set X),∀ i j,coefficientValue 2 (F i j) z =
      coefficientValue 2 (F0 i j) z+r*coefficientValue 2 (F1 i j) z) :
    nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q =
      nativeBulkMultiplierCommutatorForcingL hcalc F0 (fun _ => 0) Q+
      r • nativeBulkMultiplierCommutatorForcingL hcalc F1 (fun _ => 0) Q := by
  have hC (i : I) := nativeCoefficientH1ProductL_affine_on_ball hcalc
    (smoothMultiplierColumnJets F Q i) (smoothMultiplierColumnJets F0 Q i) (smoothMultiplierColumnJets F1 Q i) r (by
      intro z hz
      simp only [coefficientValue_smoothMultiplierColumnJets]
      simp only [h z hz,add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum])
  have hR (j : I) := coefficientMultiplier_affine_on_ball hcalc 0
    (smoothMultiplierRowJets F Q j) (smoothMultiplierRowJets F0 Q j) (smoothMultiplierRowJets F1 Q j) r (by
      intro z hz
      change coefficientValue 1 (smoothMultiplierRowJets F Q j) z =
        coefficientValue 1 (smoothMultiplierRowJets F0 Q j) z+r*coefficientValue 1 (smoothMultiplierRowJets F1 Q j) z
      simp only [coefficientValue_smoothMultiplierRowJets]
      simp only [h z hz,add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum])
  rw [nativeBulkMultiplierForcing_zero_drift,nativeBulkMultiplierForcing_zero_drift,nativeBulkMultiplierForcing_zero_drift]
  simp only [hC,hR,ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp,Finset.sum_add_distrib,← Finset.smul_sum]
  module

/-- Local C1 Taylor control of the coefficients gives a quadratic Taylor
    remainder of the actual bulk forcing; no extension norm is used. -/
theorem norm_nativeBulkMultiplierForcing_affine_remainder_local_C1
    (F F0 F1 : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3)
    (r q B : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hF0 : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-F0-r • F1) i j) z| ≤ q*r^2)
    (hF1 : ∀ i j,∀ z ∈ (ballOpens:Set X),‖gradient (coefficientValue 2 ((F-F0-r • F1) i j)) z‖ ≤ q*r^2)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B) :
    ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q-
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q-
      r • nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Q‖ ≤
      (15*nativeMultiplierForcingGradientBudget*B*q)*r^2 := by
  have hEq := nativeBulkMultiplierForcing_affine_on_ball fixedSobolevCalculus
    (F-F0) (F-F0-r • F1) F1 Q r (by
      intro z hz i j
      simp only [coefficientValue_sub_local,coefficientValue_smul,
        Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      ring)
  have hEq0 := nativeBulkMultiplierForcing_affine_on_ball fixedSobolevCalculus F (F-F0) F0 Q 1 (by
    intro z hz i j
    simp only [coefficientValue_sub_local,Pi.sub_apply]
    ring)
  rw [one_smul] at hEq0
  have hIdentity : nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q-
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q-
      r • nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Q =
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F-F0-r • F1) (fun _ => 0) Q := by
    rw [hEq0,hEq]
    abel
  rw [hIdentity]
  exact (norm_nativeBulkMultiplierForcing_local_C1 (F-F0-r • F1) Q (q*r^2) B
    (mul_nonneg hq (sq_nonneg _)) hB hF0 hF1 hQ1 hQ2).trans_eq (by ring)

end ShrinkingSpheres
