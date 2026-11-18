import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The forcing left after cancelling the genuine first adjoint correction. -/
def radialAdjointTaylorForcing (M0 M01 : E →L[ℝ] E) (M1 M11 : H →L[ℝ] H)
    (D D0 D1 T Td : H →L[ℝ] E) (r : ℝ) : H →L[ℝ] E :=
  M0.comp (D-D0-r • D1)+(M0-ContinuousLinearMap.id ℝ E-r • M01).comp D0-
    D0.comp (M1-ContinuousLinearMap.id ℝ H-r • M11)+
      r • (M0-ContinuousLinearMap.id ℝ E).comp D1+T-Td

/-- Exact adjoint Taylor cancellation. Only the first difference of the
    genuine inverse is required; an inverse remainder derivative is absent. -/
theorem radial_adjoint_taylor_cancellation
    (M0 M01 : E →L[ℝ] E) (M1 M11 Inv : H →L[ℝ] H)
    (D D0 D1 Da1 T Td : H →L[ℝ] E) (r : ℝ)
    (hInv : M1.comp Inv = ContinuousLinearMap.id ℝ H)
    (hFirst : Da1 = D1+M01.comp D0-D0.comp M11) :
    (M0.comp D+T-Td).comp Inv-D0-r • Da1 =
      (radialAdjointTaylorForcing M0 M01 M1 M11 D D0 D1 T Td r).comp Inv+
        r • Da1.comp (Inv-ContinuousLinearMap.id ℝ H) := by
  rw [hFirst]
  apply ContinuousLinearMap.ext
  intro u
  have hCancel : M1 (Inv u) = u := congrArg (fun A : H →L[ℝ] H => A u) hInv
  simp only [radialAdjointTaylorForcing,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,_root_.add_apply,_root_.sub_apply,_root_.smul_apply,
    map_add,map_sub,map_smul,hCancel]
  module

theorem norm_radialAdjointTaylorForcing_le
    (M0 M01 : E →L[ℝ] E) (M1 M11 : H →L[ℝ] H)
    (D D0 D1 T Td : H →L[ℝ] E) (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hM0 : ‖M0‖ ≤ C) (hD0 : ‖D0‖ ≤ 2) (hD1 : ‖D1‖ ≤ C)
    (hJ : ‖D-D0-r • D1‖ ≤ C*r^2)
    (hQ0 : ‖M0-ContinuousLinearMap.id ℝ E-r • M01‖ ≤ C*r^2)
    (hQ1 : ‖M1-ContinuousLinearMap.id ℝ H-r • M11‖ ≤ C*r^2)
    (hDel : ‖M0-ContinuousLinearMap.id ℝ E‖ ≤ C*r)
    (hT : ‖T‖ ≤ C*r^2) (hTd : ‖Td‖ ≤ C*r^2) :
    ‖radialAdjointTaylorForcing M0 M01 M1 M11 D D0 D1 T Td r‖ ≤ (2*C^2+6*C)*r^2 := by
  let A := M0.comp (D-D0-r • D1)
  let B := (M0-ContinuousLinearMap.id ℝ E-r • M01).comp D0
  let G := D0.comp (M1-ContinuousLinearMap.id ℝ H-r • M11)
  let V := r • (M0-ContinuousLinearMap.id ℝ E).comp D1
  have hA : ‖A‖ ≤ C^2*r^2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hM0 hJ (norm_nonneg _) hC).trans_eq (by ring))
  have hB : ‖B‖ ≤ 2*C*r^2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hQ0 hD0 (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have hG : ‖G‖ ≤ 2*C*r^2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hD0 hQ1 (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hV : ‖V‖ ≤ C^2*r^2 := by
    change ‖r • (M0-ContinuousLinearMap.id ℝ E).comp D1‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hDel hD1 (norm_nonneg _) (by positivity))) hr).trans_eq (by ring)
  have hn1 := norm_add_le A B
  have hn2 := norm_sub_le (A+B) G
  have hn3 := norm_add_le (A+B-G) V
  have hn4 := norm_add_le (A+B-G+V) T
  have hn5 := norm_sub_le (A+B-G+V+T) Td
  change ‖A+B-G+V+T-Td‖ ≤ _
  nlinarith only [hn1,hn2,hn3,hn4,hn5,hA,hB,hG,hV,hT,hTd]

end ShrinkingSpheres
