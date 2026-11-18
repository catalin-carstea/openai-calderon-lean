import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace ShrinkingSpheres

/-- Restricting each argument by a contraction does not enlarge the norm of
    a continuous bilinear form. -/
theorem norm_bilinearComp_unit_le {H E F : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : H →L[ℝ] H →L[ℝ] ℝ) (P : E →L[ℝ] H) (Q : F →L[ℝ] H)
    (D : ℝ) (hD : 0 ≤ D) (hB : ‖B‖ ≤ D) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖B.bilinearComp P Q‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ hD
  intro f z
  rw [ContinuousLinearMap.bilinearComp_apply]
  have hPf : ‖P f‖ ≤ ‖f‖ := (P.le_opNorm f).trans
    ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _))
  have hQz : ‖Q z‖ ≤ ‖z‖ := (Q.le_opNorm z).trans
    ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))
  exact (B.le_opNorm₂ _ _).trans (by gcongr)

end ShrinkingSpheres
