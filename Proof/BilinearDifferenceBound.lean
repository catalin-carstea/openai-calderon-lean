import Proof.CoordinateSprayBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace ShrinkingSpheres

lemma norm_bilinear_difference_le (L L0 : X →L[ℝ] X →L[ℝ] X) (p p0 q q0 : X) :
    ‖L p q-L0 p0 q0‖ ≤ ‖L-L0‖*‖p‖*‖q‖+
      ‖L0‖*‖p-p0‖*‖q‖+‖L0‖*‖p0‖*‖q-q0‖ := by
  have hEq : L p q-L0 p0 q0 = (L-L0) p q+L0 (p-p0) q+L0 p0 (q-q0) := by
    simp only [ContinuousLinearMap.sub_apply,map_sub,_root_.sub_apply]
    abel
  rw [hEq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_bilinear_apply_le _ _ _) (norm_bilinear_apply_le _ _ _)))
    (norm_bilinear_apply_le _ _ _))

end ShrinkingSpheres
