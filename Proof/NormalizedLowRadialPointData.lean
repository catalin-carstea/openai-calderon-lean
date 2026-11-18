import Proof.NearIdentityInverse
import Proof.NativeWeakTaylorData
import Proof.UniformLowRadialTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativePolynomialBulkMoments

def normalizedLowFirstPointBudget (Pw CP1 P : ℝ) : ℝ :=
  sphereSurfaceMass⁻¹*((CP1+9*Pw*‖fixedHarmonicH1LiftL‖)*‖fixedHarmonicH1LiftL‖)+
    (boundaryHalfMultiplierBudget*36*P)*‖fixedLowRadialL‖

def normalizedLowRemainderPointBudget (CA Pw Qw CP1 CP2 P Q : ℝ) : ℝ :=
  2*(sphereSurfaceMass⁻¹*((CA*CP2+(9*Pw+9*Qw)*CP1+9*Qw*‖fixedHarmonicH1LiftL‖)*‖fixedHarmonicH1LiftL‖)+
    (boundaryHalfMultiplierBudget*36*Q)*‖fixedLowRadialL‖+
    (boundaryHalfMultiplierBudget*78*Q)*∑ j : I,‖fixedSphereTangentialL j‖+
    (boundaryHalfMultiplierBudget*36*Q+boundaryHalfMultiplierBudget*36*P)*normalizedLowFirstPointBudget Pw CP1 P)

/-- Normalized point low-radial Taylor data from actual weak Taylor data and
    the same compact coefficient C1 bounds. Invertibility is obtained directly
    from the proved norm neighborhood of the identity. -/
theorem normalized_low_radial_point_data
    (F F0 F1 : SmoothCoefficientMatrix 2) (r CW CA Pw Qw CP1 CP2 P Q : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hCA : 0 ≤ CA) (hPw : 0 ≤ Pw) (hQw : 0 ≤ Qw)
    (hCP1 : 0 ≤ CP1) (hCP2 : 0 ≤ CP2) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (t : NativeWeakTaylorData (coefficientMatrixField 2 F) (coefficientMatrixField 2 F1) 1 r CW CA Pw Qw CP1 CP2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (s : X → ℝ) (hScalar : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = s w.val • (1:Mat))
    (hVal1 : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) z| ≤ P)
    (hDer1 : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) z‖ ≤ P)
    (hValR : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-(1:ℝ) • F0-r • F1) i j) z| ≤ Q*r^2)
    (hDerR : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-(1:ℝ) • F0-r • F1) i j)) z‖ ≤ Q*r^2)
    (hSmall : (boundaryHalfMultiplierBudget*36*Q+boundaryHalfMultiplierBudget*36*P)*r ≤ (1/2:ℝ)) :
    (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible ∧
    ‖(negativeBoundaryCoefficientMulL (normalCoefficientJet F)).inverse‖ ≤ 2 ∧
    ‖negativeBoundaryCoefficientMulL (normalCoefficientJet F)-
      (1:ℝ) • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤
        (boundaryHalfMultiplierBudget*36*Q+boundaryHalfMultiplierBudget*36*P)*r ∧
    ‖lowFirstRadialVariationL 1 F1 t.first_coefficient_bound‖ ≤ normalizedLowFirstPointBudget Pw CP1 P ∧
    ‖actualLowRadialErrorL (coefficientMatrixField 2 F) t.energy.coefficient_bound F-
      r • lowFirstRadialVariationL 1 F1 t.first_coefficient_bound‖ ≤
        normalizedLowRemainderPointBudget CA Pw Qw CP1 CP2 P Q*r^2 := by
  let M0 := negativeBoundaryCoefficientMulL (normalCoefficientJet F)
  let M1 := negativeBoundaryCoefficientMulL (normalCoefficientJet F1)
  let N1 := weakFirstConormalVariationL 1 (coefficientMatrixField 2 F1) t.first_coefficient_bound
  let CN1 := sphereSurfaceMass⁻¹*((CP1+9*Pw*‖fixedHarmonicH1LiftL‖)*‖fixedHarmonicH1LiftL‖)
  let QN := sphereSurfaceMass⁻¹*((CA*CP2+(9*Pw+9*Qw)*CP1+9*Qw*‖fixedHarmonicH1LiftL‖)*‖fixedHarmonicH1LiftL‖)
  let CM := boundaryHalfMultiplierBudget*36*P
  let QM := boundaryHalfMultiplierBudget*36*Q
  let QT := boundaryHalfMultiplierBudget*78*Q
  let DM := QM+CM
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hMult := boundaryHalfMultiplierBudget_nonneg
  have hN := norm_nonneg fixedHarmonicH1LiftL
  have hCN1 : 0 ≤ CN1 := by dsimp only [CN1];positivity
  have hQN : 0 ≤ QN := by dsimp only [QN];positivity
  have hCM : 0 ≤ CM := by dsimp only [CM];positivity
  have hQM : 0 ≤ QM := by dsimp only [QM];positivity
  have hQT : 0 ≤ QT := by dsimp only [QT];positivity
  have hDM : 0 ≤ DM := add_nonneg hQM hCM
  have hCB : 0 ≤ normalizedLowFirstPointBudget Pw CP1 P := by
    dsimp only [normalizedLowFirstPointBudget]
    positivity
  have hN1 : ‖N1‖ ≤ CN1 := by
    have hFlat : ‖TauCeti.PDE.energyFormH1L (flatCoefficientBound 1)‖ ≤ (1:ℝ) :=
      (flat_native_weak_energy_data 1 (by norm_num)).energy_bound
    exact (norm_weakFirstConormalVariationL_le 1 t.first_coefficient_bound 1 Pw CP1 (by norm_num) hPw hCP1
      hFlat t.first_energy_bound t.first_poisson_bound).trans_eq (by dsimp only [CN1];ring)
  have hNR : ‖nativeWeakConormalEndpoint (coefficientMatrixField 2 F) 0 0 t.energy.coefficient_bound sphereFischerInner-
      (1:ℝ) • fixedLowRadialL-r • N1‖ ≤ QN*r^2 := t.conormal_remainder_bound hr hCA hPw hQw hCP1 hCP2
  have hM1 : ‖M1‖ ≤ CM := (norm_negative_first_normal_coefficient_le F1 P hP hVal1 hDer1).trans_eq (by dsimp only [CM];ring)
  have hMR : ‖M0-(1:ℝ) • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-r • M1‖ ≤ QM*r^2 :=
    (norm_negative_normal_affine_remainder_le F F0 F1 1 r (Q*r^2) (by positivity) hF0 hValR hDerR).trans_eq (by dsimp only [QM];ring)
  have hMDiff : ‖M0-(1:ℝ) • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ DM*r :=
    norm_normal_first_difference_le M0 M1 1 r QM CM hr hr1 hQM hCM hMR hM1
  have hNear : ‖M0-ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ (1/2:ℝ) := by
    simpa only [one_smul] using hMDiff.trans hSmall
  obtain ⟨hInv,hInvNorm⟩ := near_identity_inverse_data M0 hNear
  have hTang (j : I) : ‖negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)‖ ≤ QT*r^2 :=
    (norm_negative_tangent_affine_remainder_le F F0 F1 1 r (Q*r^2) (by positivity)
      s hF0 hScalar hValR hDerR j).trans_eq (by dsimp only [QT];ring)
  have hFirst : ‖lowFirstRadialVariationL 1 F1 t.first_coefficient_bound‖ ≤ normalizedLowFirstPointBudget Pw CP1 P := by
    change ‖(1:ℝ)⁻¹ • (N1-M1.comp fixedLowRadialL)‖ ≤ _
    simp only [inv_one,one_smul]
    exact ((norm_sub_le _ _).trans (add_le_add hN1
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hM1 (norm_nonneg _))))).trans_eq rfl
  refine ⟨hInv,hInvNorm,hMDiff,hFirst,?_⟩
  exact norm_radialErrorAssembly_first_remainder_le _ N1 fixedLowRadialL M0 M1 _ fixedSphereTangentialL
    1 r 2 QN QM QT DM (normalizedLowFirstPointBudget Pw CP1 P) (by norm_num) hr (by norm_num)
    hQN hQM hQT hDM hCB hInv hInvNorm hNR hMR hTang hMDiff hFirst

end ShrinkingSpheres
