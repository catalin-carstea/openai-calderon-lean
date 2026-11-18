import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
namespace ShrinkingSpheres

theorem norm_sub_of_affine_remainder_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x x0 x1 : E) (r P Q : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hFirst : ‖x1‖ ≤ P) (hR : ‖x-x0-r • x1‖ ≤ Q*r^2) :
    ‖x-x0‖ ≤ (P+Q)*r := by
  have hEq : x-x0 = (x-x0-r • x1)+r • x1 := by abel
  calc
    _ = ‖(x-x0-r • x1)+r • x1‖ := congrArg norm hEq
    _ ≤ ‖x-x0-r • x1‖+‖r • x1‖ := norm_add_le _ _
    _ ≤ Q*r^2+r*P := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr];gcongr
    _ ≤ Q*r+r*P := by gcongr;nlinarith only [mul_le_mul_of_nonneg_left hr1 hr]
    _ = _ := by ring

/-- Product Taylor estimate for a varying boundary trace map and Poisson
    solution map, retaining both genuine first variations. -/
theorem norm_operator_poisson_taylor_le {U V H : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A A0 A1 : U →L[ℝ] V) (P P0 P1 : H →L[ℝ] U)
    (r D L Q C1 C2 : ℝ) (hr : 0 ≤ r) (hD : 0 ≤ D) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hA : ‖A‖ ≤ D) (hADiff : ‖A-A0‖ ≤ (L+Q)*r)
    (hAR : ‖A-A0-r • A1‖ ≤ Q*r^2)
    (hPR : ‖P-P0-r • P1‖ ≤ C2*r^2) (hP1 : ‖P1‖ ≤ C1) :
    ‖A.comp P-A0.comp P0-r • (A0.comp P1+A1.comp P0)‖ ≤
      (D*C2+(L+Q)*C1+Q*‖P0‖)*r^2 := by
  have hEq : A.comp P-A0.comp P0-r • (A0.comp P1+A1.comp P0) =
      A.comp (P-P0-r • P1)+r • (A-A0).comp P1+(A-A0-r • A1).comp P0 := by
    simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp]
    module
  have hOne : ‖A.comp (P-P0-r • P1)‖ ≤ D*C2*r^2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hA hPR (norm_nonneg _) hD).trans_eq (by ring))
  have hTwo : ‖r • (A-A0).comp P1‖ ≤ (L+Q)*C1*r^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hADiff hP1 (norm_nonneg _) (mul_nonneg (add_nonneg hL hQ) hr))) hr).trans_eq (by ring)
  have hThree : ‖(A-A0-r • A1).comp P0‖ ≤ Q*‖P0‖*r^2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right hAR (norm_nonneg _)).trans_eq (by ring))
  rw [hEq]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hOne hTwo) hThree).trans_eq (by ring))

end ShrinkingSpheres
