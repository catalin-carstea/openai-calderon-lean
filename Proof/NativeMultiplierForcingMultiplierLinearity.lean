import Proof.MultiplierForcingAffine

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

/-- The genuine forcing is affine in the gradient of its scalar multiplier;
only agreement on the physical ball is needed. -/
theorem nativeBulkMultiplierForcing_multiplier_affine_on_ball (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (Q Q0 Q1 : SmoothCoefficientJets 3) (c : ℝ)
    (h : ∀ z ∈ (ballOpens:Set X),∀ j,
      (gradient (coefficientValue 3 Q) z) j =
        (gradient (coefficientValue 3 Q0) z) j+c*(gradient (coefficientValue 3 Q1) z) j) :
    nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q =
      nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q0+
      c • nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q1 := by
  have hC (i : I) := nativeCoefficientH1ProductL_affine_on_ball hcalc
    (smoothMultiplierColumnJets F Q i) (smoothMultiplierColumnJets F Q0 i) (smoothMultiplierColumnJets F Q1 i) c (by
      intro z hz
      simp only [coefficientValue_smoothMultiplierColumnJets,h z hz,mul_add,Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring)
  have hR (j : I) := coefficientMultiplier_affine_on_ball hcalc 0
    (smoothMultiplierRowJets F Q j) (smoothMultiplierRowJets F Q0 j) (smoothMultiplierRowJets F Q1 j) c (by
      intro z hz
      change coefficientValue 1 (smoothMultiplierRowJets F Q j) z =
        coefficientValue 1 (smoothMultiplierRowJets F Q0 j) z+c*coefficientValue 1 (smoothMultiplierRowJets F Q1 j) z
      simp only [coefficientValue_smoothMultiplierRowJets,h z hz,mul_add,Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
  rw [nativeBulkMultiplierForcing_zero_drift,nativeBulkMultiplierForcing_zero_drift,nativeBulkMultiplierForcing_zero_drift]
  simp only [hC,hR,ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp,Finset.sum_add_distrib,← Finset.smul_sum]
  module

lemma coefficientValue_gradient_add (Q R : SmoothCoefficientJets 3) (z : X) :
    gradient (coefficientValue 3 (Q+R)) z =
      gradient (coefficientValue 3 Q) z+gradient (coefficientValue 3 R) z := by
  rw [coefficientValue_add]
  unfold gradient
  rw [fderiv_add ((contDiff_coefficientValue 3 Q).differentiable (by simp) z)
    ((contDiff_coefficientValue 3 R).differentiable (by simp) z),map_add]

lemma coefficientValue_gradient_smul (Q : SmoothCoefficientJets 3) (c : ℝ) (z : X) :
    gradient (coefficientValue 3 (c • Q)) z = c • gradient (coefficientValue 3 Q) z := by
  rw [coefficientValue_smul]
  unfold gradient
  rw [fderiv_const_smul ((contDiff_coefficientValue 3 Q).differentiable (by simp) z),map_smul]

lemma nativeBulkMultiplierForcing_multiplier_add (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (Q R : SmoothCoefficientJets 3) :
    nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) (Q+R) =
      nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q+
      nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) R := by
  have h := nativeBulkMultiplierForcing_multiplier_affine_on_ball hcalc F (Q+R) Q R 1 (by
    intro z hz j
    rw [coefficientValue_gradient_add]
    simp only [PiLp.add_apply,one_mul])
  simpa only [one_smul] using h

lemma nativeBulkMultiplierForcing_multiplier_smul (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) (c : ℝ) :
    nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) (c • Q) =
      c • nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q := by
  have h := nativeBulkMultiplierForcing_multiplier_affine_on_ball hcalc F (c • Q) Q Q (c-1) (by
    intro z hz j
    rw [coefficientValue_gradient_smul]
    simp only [PiLp.smul_apply,smul_eq_mul]
    ring)
  simpa only [sub_smul,one_smul,add_sub_cancel] using h

end ShrinkingSpheres
