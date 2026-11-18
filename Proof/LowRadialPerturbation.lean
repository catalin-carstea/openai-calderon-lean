import Proof.ScalarOperatorInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
namespace ShrinkingSpheres

/-- Solving the normal/tangential conormal decomposition for the radial error. -/
def radialErrorAssembly {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (M : F →L[ℝ] F) (D : E →L[ℝ] F)
    (T : Fin 3 → F →L[ℝ] F) (G : Fin 3 → E →L[ℝ] F) : E →L[ℝ] F :=
  M.inverse.comp (A-M.comp D-∑ j : Fin 3,(T j).comp (G j))

/-- The conormal error and the coefficient perturbations give the low radial
    endpoint with a radius-linear bound. -/
theorem norm_radialErrorAssembly_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (M : F →L[ℝ] F) (D : E →L[ℝ] F)
    (T : Fin 3 → F →L[ℝ] F) (G : Fin 3 → E →L[ℝ] F)
    (c r CI CA CM CT : ℝ) (hr : 0 ≤ r)
    (hCI : 0 ≤ CI) (hCA : 0 ≤ CA) (hCM : 0 ≤ CM) (hCT : 0 ≤ CT)
    (hInv : ‖M.inverse‖ ≤ CI) (hA : ‖A-c • D‖ ≤ CA*r)
    (hM : ‖M-c • ContinuousLinearMap.id ℝ F‖ ≤ CM*r)
    (hT : ∀ j,‖T j‖ ≤ CT*r) :
    ‖radialErrorAssembly A M D T G‖ ≤
      CI*(CA+CM*‖D‖+CT*∑ j : Fin 3,‖G j‖)*r := by
  have hEq : A-M.comp D = (A-c • D)-(M-c • ContinuousLinearMap.id ℝ F).comp D := by
    rw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp,ContinuousLinearMap.id_comp]
    abel
  have hMain : ‖A-M.comp D‖ ≤ (CA+CM*‖D‖)*r := by
    rw [hEq]
    calc
      _ ≤ ‖A-c • D‖+‖(M-c • ContinuousLinearMap.id ℝ F).comp D‖ := norm_sub_le _ _
      _ ≤ CA*r+(CM*r)*‖D‖ := add_le_add hA
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right hM (norm_nonneg _)))
      _ = _ := by ring
  have hSum : ‖∑ j : Fin 3,(T j).comp (G j)‖ ≤ CT*(∑ j : Fin 3,‖G j‖)*r := by
    calc
      _ ≤ ∑ j : Fin 3,‖(T j).comp (G j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3,(CT*r)*‖G j‖ := Finset.sum_le_sum fun j _ =>
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hT j) (norm_nonneg _))
      _ = _ := by rw [← Finset.mul_sum];ring
  have hInside : ‖A-M.comp D-∑ j : Fin 3,(T j).comp (G j)‖ ≤
      (CA+CM*‖D‖+CT*∑ j : Fin 3,‖G j‖)*r :=
    (norm_sub_le _ _).trans ((add_le_add hMain hSum).trans_eq (by ring))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hInv hInside (norm_nonneg _) hCI).trans_eq (by ring))

end ShrinkingSpheres
