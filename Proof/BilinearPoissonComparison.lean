import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 15
namespace ShrinkingSpheres

/-- Quantitative comparison of the boundary energy forms induced by two
    Poisson lifts, in a general real normed space. -/
theorem norm_bilinear_poisson_difference_le
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B B0 : H →L[ℝ] H →L[ℝ] ℝ) (P P0 : F →L[ℝ] H)
    (C D q : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hB : ‖B‖ ≤ D) (hDeltaB : ‖B-B0‖ ≤ q)
    (hDeltaP : ‖P-P0‖ ≤ C*q*‖P0‖) :
    ‖B.bilinearComp P P0-B0.bilinearComp P0 P0‖ ≤ (D*C+1)*q*‖P0‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro f z
  simp only [_root_.sub_apply,ContinuousLinearMap.bilinearComp_apply]
  have hAlg : B (P f) (P0 z)-B0 (P0 f) (P0 z) =
      B (P f-P0 f) (P0 z)+(B-B0) (P0 f) (P0 z) := by
    simp only [map_sub,_root_.sub_apply]
    ring
  rw [hAlg]
  have hPdiff : ‖P f-P0 f‖ ≤ (C*q*‖P0‖)*‖f‖ :=
    ((P-P0).le_opNorm f).trans (mul_le_mul_of_nonneg_right hDeltaP (norm_nonneg f))
  have hFirst : ‖B (P f-P0 f) (P0 z)‖ ≤ D*‖P f-P0 f‖*‖P0 z‖ :=
    (B.le_opNorm₂ _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) (norm_nonneg _))
  have hSecond : ‖(B-B0) (P0 f) (P0 z)‖ ≤ q*‖P0 f‖*‖P0 z‖ :=
    ((B-B0).le_opNorm₂ _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDeltaB (norm_nonneg _)) (norm_nonneg _))
  calc
    _ ≤ ‖B (P f-P0 f) (P0 z)‖+‖(B-B0) (P0 f) (P0 z)‖ := norm_add_le _ _
    _ ≤ D*‖P f-P0 f‖*‖P0 z‖+q*‖P0 f‖*‖P0 z‖ := add_le_add hFirst hSecond
    _ ≤ D*((C*q*‖P0‖)*‖f‖)*(‖P0‖*‖z‖)+q*(‖P0‖*‖f‖)*(‖P0‖*‖z‖) := by
      gcongr
      · exact P0.le_opNorm z
      · exact P0.le_opNorm f
      · exact P0.le_opNorm z
    _ = _ := by ring

/-- Scalar multiplication bound kept abstract so coefficient proofs do not
    expand their inherited operator-space structures to use it. -/
theorem norm_nonneg_smul_bilinear_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (t : ℝ) (ht : 0 ≤ t) (B : F →L[ℝ] F →L[ℝ] ℝ) (q : ℝ) (hB : ‖B‖ ≤ q) :
    ‖t • B‖ ≤ t*q := by
  have hs : ‖t • B‖ ≤ t*‖B‖ := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg ht] using norm_smul_le t B
  exact hs.trans (mul_le_mul_of_nonneg_left hB ht)

end ShrinkingSpheres
