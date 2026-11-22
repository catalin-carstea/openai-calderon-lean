module

public import Proof.CalderonN.CoordinateSprayBounds

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/BilinearDifferenceBound.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma norm_bilinear_difference_le (L L0 : (X dim) →L[ℝ] (X dim) →L[ℝ] (X dim)) (p p0 q q0 : (X dim)) :
    ‖L p q-L0 p0 q0‖ ≤ ‖L-L0‖*‖p‖*‖q‖+
      ‖L0‖*‖p-p0‖*‖q‖+‖L0‖*‖p0‖*‖q-q0‖ := by
  have hEq : L p q-L0 p0 q0 = (L-L0) p q+L0 (p-p0) q+L0 p0 (q-q0) := by
    simp only [ContinuousLinearMap.sub_apply,map_sub,_root_.sub_apply]
    abel
  rw [hEq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_bilinear_apply_le _ _ _) (norm_bilinear_apply_le _ _ _)))
    (norm_bilinear_apply_le _ _ _))

end CalderonN
