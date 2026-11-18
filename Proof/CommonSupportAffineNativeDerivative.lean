import Proof.CommonSupportAffineOperatorFamilies
import Proof.CommonSupportDirectionalGenerators
import Proof.AffineWeakEnergyFamilyIdentity
import Proof.AffineFamilyDerivativeBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL fullCoefficientOperatorL strongCoefficientOperatorL

lemma norm_affine_derivative_scaled_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A A1 D : ℝ → E) (A0 : E) (r k q1 qD : ℝ)
    (hFamily : ∀ t,A t = A0+r • A1 t+D t)
    (hA1 : DifferentiableAt ℝ A1 0) (hD : DifferentiableAt ℝ D 0)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hk : 0 ≤ k) (hq1 : 0 ≤ q1) (hqD : 0 ≤ qD)
    (hN1 : ‖fderiv ℝ A1 0‖ ≤ k*q1) (hND : ‖fderiv ℝ D 0‖ ≤ k*(qD*r^2)) :
    ‖fderiv ℝ A 0‖ ≤ k*((q1+qD)*r) := by
  have hb := affine_family_derivative_budget A A1 D A0 0 r (k*q1) (k*qD) hFamily hA1 hD hr hr1
    (mul_nonneg hk hq1) (mul_nonneg hk hqD) hN1 (hND.trans_eq (by ring))
  exact hb.1.trans_eq (by ring)

private lemma affine_eq_of_sub {E : Type*} [AddCommGroup E] [Module ℝ E] (A A1 D : E) (r : ℝ)
    (h : A-r • A1 = D) : A = 0+r • A1+D := by rw [← h];module

/-- The principal family inherits radius-linear native derivatives from its
    actual first model and quadratic residual, with every witness retained. -/
theorem commonSupport_affine_native_derivative_bounds
    (a a1 aD : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r q1 qD : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hq1 : 0 ≤ q1) (hqD : 0 ≤ qD)
    (hField : ∀ p,aD p = a p-r • a1 p)
    (hN1 : CommonSupportNativeDerivativeBounds a1 ha1 S1 hS1 hz1 q1)
    (hND : CommonSupportNativeDerivativeBounds aD haD SD hSD hzD (qD*r^2)) :
    CommonSupportNativeDerivativeBounds a ha S hS hz ((q1+qD)*r) := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
  have hOps := commonSupport_operator_sub_smul_families a a1 aD ha ha1 haD S S1 SD hS hS1 hSD hz hz1 hzD r hField
  have hAffine (p) (z) (_ : z ∈ (ballOpens:Set X)) : a (p,z) = (0:ℝ) • (1:Mat)+r • a1 (p,z)+aD (p,z) := by
    rw [hField];module
  have hWeak := commonSupport_weakEnergy_affine_families a a1 aD ha ha1 haD 0 r hAffine
  have hSB : 0 ≤ 2*strongC1OperatorBudget fixedSobolevCalculus :=
    mul_nonneg (by norm_num) (strongC1OperatorBudget_nonneg _)
  have hFB : 0 ≤ 2*fullC1OperatorBudget fixedSobolevCalculus :=
    mul_nonneg (by norm_num) (fullC1OperatorBudget_nonneg _)
  have hWB := weakFullDerivativeBudget_nonneg
  have hNB : 0 ≤ boundaryHalfDerivativeBudget*36 := mul_nonneg boundaryHalfDerivativeBudget_nonneg (by norm_num)
  have hTB : 0 ≤ boundaryHalfDerivativeBudget*78 := mul_nonneg boundaryHalfDerivativeBudget_nonneg (by norm_num)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact norm_affine_derivative_scaled_le _ _ _ 0 r (2*strongC1OperatorBudget fixedSobolevCalculus) q1 qD
      (fun t => affine_eq_of_sub _ _ _ r (hOps.1 t))
      ((contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a1 ha1 S1 hS1 hz1).differentiable (by simp) 0)
      ((contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 aD haD SD hSD hzD).differentiable (by simp) 0)
      hr hr1 hSB hq1 hqD hN1.strong hND.strong
  · exact norm_affine_derivative_scaled_le _ _ _ 0 r (2*fullC1OperatorBudget fixedSobolevCalculus) q1 qD
      (fun t => affine_eq_of_sub _ _ _ r (hOps.2.1 t))
      ((contDiff_commonSupport_fullCoefficientOperator 0 a1 ha1 S1 hS1 hz1).differentiable (by simp) 0)
      ((contDiff_commonSupport_fullCoefficientOperator 0 aD haD SD hSD hzD).differentiable (by simp) 0)
      hr hr1 hFB hq1 hqD hN1.full hND.full
  · exact norm_affine_derivative_scaled_le _ _ _ _ r weakFullDerivativeBudget q1 qD hWeak.1
      ((contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0)
      ((contDiff_commonSupportFullWeakEnergy aD haD SD hSD hzD).differentiable (by simp) 0)
      hr hr1 hWB hq1 hqD hN1.fullWeak hND.fullWeak
  · exact norm_affine_derivative_scaled_le _ _ _ _ r weakFullDerivativeBudget q1 qD hWeak.2.1
      ((contDiff_commonSupportWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0)
      ((contDiff_commonSupportWeakEnergy aD haD SD hSD hzD).differentiable (by simp) 0)
      hr hr1 hWB hq1 hqD hN1.weak hND.weak
  · exact norm_affine_derivative_scaled_le _ _ _ _ r weakFullDerivativeBudget q1 qD hWeak.2.2
      ((contDiff_commonSupportZeroWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0)
      ((contDiff_commonSupportZeroWeakEnergy aD haD SD hSD hzD).differentiable (by simp) 0)
      hr hr1 hWB hq1 hqD hN1.zeroWeak hND.zeroWeak
  · have hb := norm_affine_derivative_scaled_le _ _ _ 0 r (boundaryHalfDerivativeBudget*36) q1 qD
      (fun t => affine_eq_of_sub _ _ _ r (hOps.2.2.1 t))
      ((contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace a1 ha1 S1 hS1 hz1).differentiable (by simp) 0)
      ((contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace aD haD SD hSD hzD).differentiable (by simp) 0)
      hr hr1 hNB hq1 hqD (hN1.normal.trans_eq (by ring)) (hND.normal.trans_eq (by ring))
    exact hb.trans_eq (by ring)
  · intro j
    have hb := norm_affine_derivative_scaled_le _ _ _ 0 r (boundaryHalfDerivativeBudget*78) q1 qD
      (fun t => affine_eq_of_sub _ _ _ r (hOps.2.2.2 j t))
      ((contDiff_negativeHalf_tangentCoefficientFamily fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace a1 ha1 S1 hS1 hz1 j).differentiable (by simp) 0)
      ((contDiff_negativeHalf_tangentCoefficientFamily fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace aD haD SD hSD hzD j).differentiable (by simp) 0)
      hr hr1 hTB hq1 hqD ((hN1.tangent j).trans_eq (by ring)) ((hND.tangent j).trans_eq (by ring))
    exact hb.trans_eq (by ring)

end ShrinkingSpheres
