module

public import Proof.CalderonN.TraceFrameCoefficients

import Mathlib.Tactic

/-! A coordinate bound controls a scalar multilinear form in the
Euclidean chart. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CalderonN

variable {dim n : ℕ} [NeZero dim]

theorem norm_multilinear_le_of_chart_components
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => X dim) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i : Fin n → I dim,|T (fun j => axis (i j))| ≤ C) :
    ‖T‖ ≤ (dim:ℝ)^n*C := by
  classical
  apply T.opNorm_le_bound (by positivity)
  intro v
  have hEq : T v = ∑ i : Fin n → I dim,(∏ j : Fin n,v j (i j)) • T (fun j => axis (i j)) := by
    have hv : v = fun j => ∑ i : I dim,v j i • axis i :=
      funext fun j => (axis_sum_chart (v j)).symm
    conv_lhs => rw [hv]
    change T.toMultilinearMap (fun j => ∑ i : I dim,v j i • axis i) = _
    rw [T.toMultilinearMap.map_sum]
    simp only [MultilinearMap.map_smul_univ,ContinuousMultilinearMap.coe_coe]
  rw [hEq]
  calc
    _ ≤ ∑ i : Fin n → I dim, ‖(∏ j : Fin n,v j (i j)) • T (fun j => axis (i j))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n → I dim,(∏ j : Fin n,‖v j‖)*C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,Finset.abs_prod]
      apply mul_le_mul _ (h i) (abs_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro j _
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v j) (i j)
    _ = _ := by
      simp
      ring

end CalderonN
