import Proof.NormalizedLowRadialPointData
import Proof.CommonSupportLowRadialDerivativeData
import Proof.LowRadialCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse
  fullCoefficientOperatorL strongCoefficientOperatorL strongDirichletOperator commonSupportMatrixFamily

/-- Shared low-endpoint assembly from actual normalized point and native
    derivative data. Both center and relative-radius callers use the same
    coefficient witnesses and the same local coercive/normal inverse construction. -/
theorem exists_commonSupport_low_radial_taylor_data
    (CW CA P Q CP1 CP2 PS QS CN C1 CQ : ℝ)
    (hCA : 0 ≤ CA) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hCP1 : 0 ≤ CP1) (hCP2 : 0 ≤ CP2)
    (hPS : 0 ≤ PS) (hQS : 0 ≤ QS) (hCN : 0 ≤ CN) (hC1 : 0 ≤ C1) (hCQ : 0 ≤ CQ) :
    ∃ δ CLow : ℝ,0 < δ ∧ 0 ≤ CLow ∧
      ∀ (A A1 : ℝ × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
      (S : Set X) (hS : IsCompact S) (hz : ∀ t z,z ∉ S → A (t,z) = 0)
      (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0) (r L : ℝ),
      0 ≤ r → r ≤ 1 → r ≤ δ → 0 ≤ L →
      ∀ (F0 F0S : SmoothCoefficientMatrix 2),
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0S z = 1) →
      ∀ s : X → ℝ,
      (∀ w : UnitSphere,coefficientMatrixField 2 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0) w.val = s w.val • (1:Mat)) →
      NativeWeakTaylorData (fun z => A (0,z)) (fun z => A1 (0,z)) 1 r CW CA P Q CP1 CP2 →
      CommonSupportNativeDerivativeBounds A hA S hS hz ((C1+CQ)*r*L) →
      CommonSupportNativeDerivativeBounds A1 hA1 S hS hz1 (C1*L) →
      CommonSupportTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 r F0 (CQ*r^2*L) →
      (∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0 i j) z| ≤ PS) →
      (∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0 i j)) z‖ ≤ PS) →
      (∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2
        ((commonSupportMatrixFamily 2 A hA S hS hz 0-F0S-r • commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0) i j) z| ≤ QS*r^2) →
      (∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2
        ((commonSupportMatrixFamily 2 A hA S hS hz 0-F0S-r • commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0) i j)) z‖ ≤ QS*r^2) →
      ‖fderiv ℝ (fun t => commonSupportWeakConormalEndpoint A hA t-(1:ℝ) • fixedLowRadialL-
        r • weakFirstConormalVariationL 1 (fun z => A1 (t,z)) (commonSupportEnergyMemLp A1 hA1 t)) 0‖ ≤ CN*r^2*L →
      ∃ W : Set ℝ,IsOpen W ∧ (0:ℝ) ∈ W ∧
        (∀ t ∈ W,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA t))) ∧
        (∀ t ∈ W,(negativeBoundaryCoefficientMulL
          (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz t))).IsInvertible) ∧
        DifferentiableAt ℝ (fun t => commonSupportLowRadialErrorL A hA S hS hz t-
          r • commonSupportLowFirstRadialL A1 hA1 S hS hz1 1 t) 0 ∧
        ‖fderiv ℝ (fun t => commonSupportLowRadialErrorL A hA S hS hz t-
          r • commonSupportLowFirstRadialL A1 hA1 S hS hz1 1 t) 0‖ ≤ CLow*r^2*L := by
  let DM := boundaryHalfMultiplierBudget*36*QS+boundaryHalfMultiplierBudget*36*PS
  let CB := normalizedLowFirstPointBudget P CP1 PS
  let CL := normalizedLowRemainderPointBudget CA P Q CP1 CP2 PS QS
  let CP := 2+DM+CB+|CL|
  let CD1 := boundaryHalfDerivativeBudget*(36*C1)
  let CDQ := boundaryHalfDerivativeBudget*(36*CQ)
  let CDT := boundaryHalfDerivativeBudget*(78*CQ)
  let CDM := boundaryHalfDerivativeBudget*(36*(C1+CQ))
  let CDE := weakFullDerivativeBudget*C1
  let CD := CN+CD1+CDQ+CDT+CDM+CDE
  let CLow := lowRadialAngleDerivativeBudget 1 CP CD
  have hMB := boundaryHalfMultiplierBudget_nonneg
  have hDB := boundaryHalfDerivativeBudget_nonneg
  have hWB := weakFullDerivativeBudget_nonneg
  have hN := norm_nonneg fixedHarmonicH1LiftL
  have hArea := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hDM : 0 ≤ DM := by dsimp only [DM];positivity
  have hCB : 0 ≤ CB := by dsimp only [CB,normalizedLowFirstPointBudget];positivity
  have hCLabs : 0 ≤ |CL| := abs_nonneg CL
  have hCP : 0 ≤ CP := by dsimp only [CP];positivity
  have hCPtwo : (2:ℝ) ≤ CP := by dsimp only [CP];linarith only [hDM,hCB,hCLabs]
  have hCPDM : DM ≤ CP := by dsimp only [CP];linarith only [hCB,hCLabs]
  have hCPCB : CB ≤ CP := by dsimp only [CP];linarith only [hDM,hCLabs]
  have hCPCL : CL ≤ CP := by dsimp only [CP];linarith only [hDM,hCB,le_abs_self CL]
  have hCD10 : 0 ≤ CD1 := by dsimp only [CD1];positivity
  have hCDQ0 : 0 ≤ CDQ := by dsimp only [CDQ];positivity
  have hCDT0 : 0 ≤ CDT := by dsimp only [CDT];positivity
  have hCDM0 : 0 ≤ CDM := by dsimp only [CDM];positivity
  have hCDE0 : 0 ≤ CDE := by dsimp only [CDE];positivity
  have hCD : 0 ≤ CD := by dsimp only [CD];positivity
  have hCNC : CN ≤ CD := by dsimp only [CD];linarith only [hCD10,hCDQ0,hCDT0,hCDM0,hCDE0]
  have hCD1 : CD1 ≤ CD := by dsimp only [CD];linarith only [hCN,hCDQ0,hCDT0,hCDM0,hCDE0]
  have hCDQ : CDQ ≤ CD := by dsimp only [CD];linarith only [hCN,hCD10,hCDT0,hCDM0,hCDE0]
  have hCDT : CDT ≤ CD := by dsimp only [CD];linarith only [hCN,hCD10,hCDQ0,hCDM0,hCDE0]
  have hCDM : CDM ≤ CD := by dsimp only [CD];linarith only [hCN,hCD10,hCDQ0,hCDT0,hCDE0]
  have hCDE : CDE ≤ CD := by dsimp only [CD];linarith only [hCN,hCD10,hCDQ0,hCDT0,hCDM0]
  have hCLow : 0 ≤ CLow := lowRadialAngleDerivativeBudget_nonneg 1 CP CD (by norm_num) hCP hCD
  let δ := 1/(2*(DM+1))
  have hδ : 0 < δ := by dsimp only [δ];positivity
  refine ⟨δ,CLow,hδ,hCLow,?_⟩
  intro A A1 hA hA1 S hS hz hz1 r L hr hr1 hrδ hL F0 F0S hF0S s hScalar hPoint hNA hN1 hTaylor hVal1 hDer1 hValR hDerR hDN
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let F1 := commonSupportMatrixFamily 2 A1 hA1 S hS hz1
  have hNear : DM*r ≤ (1/2:ℝ) := by
    have hRDM : r*(2*(DM+1)) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 2*(DM+1))).mp hrδ
    nlinarith only [hRDM,hr]
  have hPointF : NativeWeakTaylorData (coefficientMatrixField 2 (F 0)) (coefficientMatrixField 2 (F1 0))
      1 r CW CA P Q CP1 CP2 := by
    simpa only [F,F1,coefficientMatrixField_commonSupportMatrixFamily] using hPoint
  obtain ⟨hNormal,hNorm,hDiff,hB,hJ⟩ := normalized_low_radial_point_data (F 0) F0S (F1 0) r CW CA P Q CP1 CP2 PS QS
    hr hr1 hCA hP hQ hCP1 hCP2 hPS hQS hPointF hF0S s hScalar
    hVal1 hDer1 (by simpa only [one_smul] using hValR) (by simpa only [one_smul] using hDerR) hNear
  have hNormal0 : (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily A hA S hS hz 0)).IsInvertible := by
    rw [commonSupport_negative_normal_multiplier_eq]
    exact hNormal
  have hMINorm : ‖(negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily A hA S hS hz 0)).inverse‖ ≤ CP := by
    rw [commonSupport_negative_normal_multiplier_eq]
    exact hNorm.trans hCPtwo
  have hMDiff : ‖negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily A hA S hS hz 0)-
      (1:ℝ) • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ CP*r := by
    rw [commonSupport_negative_normal_multiplier_eq]
    exact hDiff.trans (mul_le_mul_of_nonneg_right hCPDM hr)
  have hFirstEq := commonSupport_lowFirstRadial_eq_of_coefficient A1 hA1 S hS hz1 0 1 (F1 0)
    hPointF.first_coefficient_bound (fun z _ => congrArg (fun f : X → Mat => f z)
      (coefficientMatrixField_commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0).symm)
  have hBPoint : ‖commonSupportLowFirstRadialL A1 hA1 S hS hz1 1 0‖ ≤ CP := by
    rw [hFirstEq]
    exact hB.trans hCPCB
  have hJPoint : ‖commonSupportLowRadialErrorL A hA S hS hz 0-
      r • commonSupportLowFirstRadialL A1 hA1 S hS hz1 1 0‖ ≤ CP*r^2 := by
    have hJ' : ‖commonSupportLowRadialErrorL A hA S hS hz 0-
      r • commonSupportLowFirstRadialL A1 hA1 S hS hz1 1 0‖ ≤ CL*r^2 := by
      rw [hFirstEq]
      simpa only [commonSupportLowRadialErrorL,F,F1,coefficientMatrixField_commonSupportMatrixFamily] using hJ
    exact hJ'.trans (mul_le_mul_of_nonneg_right hCPCL (sq_nonneg r))
  have hCNBound := hDN.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCNC (sq_nonneg r)) hL)
  obtain ⟨W,hW,h0W,hCoercive,hNormalW,hLowDiff,hLow⟩ := commonSupport_low_radial_derivative_data
    A A1 hA hA1 S S hS hS hz hz1 r C1 CQ CP CD L hr hr1 hCP hCD hL F0
    hNA hN1 hTaylor hCD1 hCDQ hCDT hCDM hCDE hPoint.energy.coercive hNormal0 hMINorm hMDiff hBPoint hJPoint hCNBound
  exact ⟨W,hW,h0W,hCoercive,hNormalW,hLowDiff,hLow⟩

end ShrinkingSpheres
