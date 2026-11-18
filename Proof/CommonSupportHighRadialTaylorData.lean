import Proof.StrongAffineOperatorPointBounds
import Proof.CommonSupportTaylorDerivativeData
import Proof.StrongPoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL

def commonSupportHighRadialDerivativeBudget (CI P Q C1 CQ : ℝ) : ℝ :=
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let FB := fullC1OperatorBudget fixedSobolevCalculus
  let DA := 2*SB*(C1+CQ)
  let D1 := 2*FB*C1
  let DQ := 2*FB*CQ
  let DB := SB*(Q+P)
  let V1 := FB*P
  let CS := CI*(FB*Q+CI*DB*V1)*‖fixedHarmonicLiftL‖
‖fixedHalfOutwardTraceL‖*CI*
    ((DQ+DA*CI*V1+DB*CI*D1)*‖fixedHarmonicLiftL‖+DA*CS)

lemma commonSupportHighRadialDerivativeBudget_nonneg (CI P Q C1 CQ : ℝ)
    (hCI : 0 ≤ CI) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hC1 : 0 ≤ C1) (hCQ : 0 ≤ CQ) :
    0 ≤ commonSupportHighRadialDerivativeBudget CI P Q C1 CQ := by
  have hSB := strongC1OperatorBudget_nonneg fixedSobolevCalculus
  have hFB := fullC1OperatorBudget_nonneg fixedSobolevCalculus
  dsimp only [commonSupportHighRadialDerivativeBudget]
  positivity

/-- The same native principal/first/residual derivative data and actual strong
    point Taylor bounds supply the high radial quadratic derivative, together
    with its genuine local strong inverse locus. -/
theorem commonSupport_high_radial_taylor_derivative_data
    (A A1 : ℝ × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S : Set X) (hS : IsCompact S) (hz : ∀ t z,z ∉ S → A (t,z) = 0)
    (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0)
    (r CI P Q C1 CQ L : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCI : 0 ≤ CI) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hC1 : 0 ≤ C1) (hCQ : 0 ≤ CQ) (hL : 0 ≤ L)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hNative : CommonSupportNativeDerivativeBounds A hA S hS hz ((C1+CQ)*r*L))
    (hNative1 : CommonSupportNativeDerivativeBounds A1 hA1 S hS hz1 (C1*L))
    (hTaylor : CommonSupportTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 r F0 (CQ*r^2*L))
    (hInvPoint : (strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 A hA S hS hz 0)).IsInvertible)
    (hInvNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 A hA S hS hz 0)).inverse‖ ≤ CI)
    (hInvBase : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (hBaseNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ CI)
    (hVal1 : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0 i j) z| ≤ P)
    (hDer1 : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0 i j)) z‖ ≤ P)
    (hValR : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2
      ((commonSupportMatrixFamily 2 A hA S hS hz 0-F0-r • commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0) i j) z| ≤ Q*r^2)
    (hDerR : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2
      ((commonSupportMatrixFamily 2 A hA S hS hz 0-F0-r • commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0) i j)) z‖ ≤ Q*r^2) :
    ∃ U : Set ℝ,IsOpen U ∧ (0:ℝ) ∈ U ∧
      (∀ t ∈ U,(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 A hA S hS hz t)).IsInvertible) ∧
      ‖fderiv ℝ (fun t => actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz t)-
        r • highFirstRadialVariationL F0 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 t) 1) 0‖ ≤
          commonSupportHighRadialDerivativeBudget CI P Q C1 CQ*r^2*L := by
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let FB := fullC1OperatorBudget fixedSobolevCalculus
  let DA := 2*SB*(C1+CQ)
  let D1 := 2*FB*C1
  let DQ := 2*FB*CQ
  let DB := SB*(Q+P)
  let V1 := FB*P
  let CS := CI*(FB*Q+CI*DB*V1)*‖fixedHarmonicLiftL‖
  let C := ‖fixedHalfOutwardTraceL‖*CI*
    ((DQ+DA*CI*V1+DB*CI*D1)*‖fixedHarmonicLiftL‖+DA*CS)
  have hSB : 0 ≤ SB := strongC1OperatorBudget_nonneg _
  have hFB : 0 ≤ FB := fullC1OperatorBudget_nonneg _
  have hDA : 0 ≤ DA := by dsimp [DA];positivity
  have hD1 : 0 ≤ D1 := by dsimp [D1];positivity
  have hDQ : 0 ≤ DQ := by dsimp [DQ];positivity
  have hDB : 0 ≤ DB := by dsimp [DB];positivity
  have hV1 : 0 ≤ V1 := by dsimp [V1];positivity
  have hCS : 0 ≤ CS := by dsimp [CS];positivity
  have hC : 0 ≤ C := by dsimp [C];positivity
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let F1 := commonSupportMatrixFamily 2 A1 hA1 S hS hz1
  have hOpsPoint := strong_affine_operator_point_bounds fixedSobolevCalculus (F 0) F0 (F1 0) 1 r P Q hP hQ hr hr1
    hVal1 hDer1 (by simpa only [one_smul] using hValR) (by simpa only [one_smul] using hDerR)
  have hASmooth : ContDiff ℝ ∞ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)) :=
    contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 A hA S hS hz
  have hTSmooth : ContDiff ℝ ∞ (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F t)) :=
    contDiff_commonSupport_fullCoefficientOperator 0 A hA S hS hz
  have hT1Smooth : ContDiff ℝ ∞ (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t)) :=
    contDiff_commonSupport_fullCoefficientOperator 0 A1 hA1 S hS hz1
  let U := {t : ℝ | (strongDirichletOperator fixedSobolevCalculus 0 (F t)).IsInvertible}
  have hU : IsOpen U := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hASmooth.continuous
  have h0U : (0:ℝ) ∈ U := hInvPoint
  have hInv : ∀ t ∈ U,(strongDirichletOperator fixedSobolevCalculus 0 (F t)).IsInvertible := fun t ht => ht
  have hInvBase1 : (strongDirichletOperator fixedSobolevCalculus 0 ((1:ℝ) • F0)).IsInvertible := by
    simpa only [one_smul] using hInvBase
  have hBaseNorm1 : ‖(strongDirichletOperator fixedSobolevCalculus 0 ((1:ℝ) • F0)).inverse‖ ≤ CI := by
    simpa only [one_smul] using hBaseNorm
  have hBulk : ‖strongPoissonL (F 0)-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 (F1 0) 1‖ ≤ CS*r^2 :=
    (norm_strongPoisson_first_remainder_le (F 0) F0 (F1 0) 1 r CI CI DB V1 (FB*Q) hr hCI hCI hDB hV1
      (mul_nonneg hFB hQ) (fun z hzB => hF0 z (unitBall_subset_closedBall_two hzB)) hInvPoint hInvBase1
      hInvNorm hBaseNorm1 hOpsPoint.2.1 hOpsPoint.1 hOpsPoint.2.2)
  have hNDA : ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)) 0‖ ≤ (DA*L)*r :=
    hNative.strong.trans_eq (by dsimp only [DA,SB];ring)
  have hND1 : ‖fderiv ℝ (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t)) 0‖ ≤ D1*L :=
    hNative1.full.trans_eq (by dsimp only [D1,FB];ring)
  have hNDQ : ‖fderiv ℝ (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F t)-
      fullCoefficientOperatorL fixedSobolevCalculus 0 ((1:ℝ) • F0)-r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t)) 0‖ ≤ (DQ*L)*r^2 := by
    simpa only [one_smul] using hTaylor.full.trans_eq (by dsimp only [DQ,FB];ring)
  have hHigh := norm_actual_highRadial_first_remainder_derivative_le F F1 F0 1 r 0 U hU h0U
    (fun z hzB => hF0 z (unitBall_subset_closedBall_two hzB)) hInv hInvBase1
    (hASmooth.differentiable (by simp) 0) (hTSmooth.differentiable (by simp) 0) (hT1Smooth.differentiable (by simp) 0)
    CI CI (DA*L) DB V1 (D1*L) (DQ*L) CS hr hr1 hCI hCI (by positivity) hDB hV1
    (by positivity) (by positivity) hCS hInvNorm hBaseNorm1 hNDA hOpsPoint.2.1 hOpsPoint.1 hND1 hNDQ hBulk
  refine ⟨U,hU,h0U,hInv,hHigh.trans_eq ?_⟩
  dsimp only [commonSupportHighRadialDerivativeBudget,SB,FB,DA,D1,DQ,DB,V1,CS]
  ring

end ShrinkingSpheres
