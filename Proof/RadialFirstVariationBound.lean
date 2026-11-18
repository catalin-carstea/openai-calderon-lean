import Proof.RadialTaylorLeftIdentity
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
namespace ShrinkingSpheres

/-- Quadratic radial remainder after the conormal and normal coefficient first
    variations. The first tangential term vanishes in the scalar affine model. -/
theorem norm_radialErrorAssembly_first_remainder_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N N1 D : E →L[ℝ] F) (M M1 : F →L[ℝ] F)
    (T : Fin 3 → F →L[ℝ] F) (G : Fin 3 → E →L[ℝ] F)
    (c r CI QN QM QT DM CB : ℝ) (hc : c ≠ 0) (hr : 0 ≤ r)
    (hCI : 0 ≤ CI) (hQN : 0 ≤ QN) (hQM : 0 ≤ QM) (hQT : 0 ≤ QT)
    (hDM : 0 ≤ DM) (hCB : 0 ≤ CB) (hM : M.IsInvertible)
    (hInv : ‖M.inverse‖ ≤ CI)
    (hN : ‖N-c • D-r • N1‖ ≤ QN*r^2)
    (hNormal : ‖M-c • ContinuousLinearMap.id ℝ F-r • M1‖ ≤ QM*r^2)
    (hT : ∀ j,‖T j‖ ≤ QT*r^2)
    (hDiff : ‖M-c • ContinuousLinearMap.id ℝ F‖ ≤ DM*r)
    (hFirst : ‖c⁻¹ • (N1-M1.comp D)‖ ≤ CB) :
    ‖radialErrorAssembly N M D T G-r • (c⁻¹ • (N1-M1.comp D))‖ ≤
      CI*(QN+QM*‖D‖+QT*∑ j : Fin 3,‖G j‖+DM*CB)*r^2 := by
  let B := c⁻¹ • (N1-M1.comp D)
  let S := ∑ j : Fin 3,(T j).comp (G j)
  have hEq : radialErrorAssembly N M D T G-r • B =
      M.inverse.comp ((N-c • D-r • N1)-
        (M-c • ContinuousLinearMap.id ℝ F-r • M1).comp D-S-
          r • (M-c • ContinuousLinearMap.id ℝ F).comp B) := by
    have hLeft := radialErrorAssembly_first_remainder_left_identity N N1 D M M1 T G c r hc hM
    have hSolve := congrArg (fun Q : E →L[ℝ] F => M.inverse.comp Q) hLeft
    change M.inverse.comp (M.comp (radialErrorAssembly N M D T G-r • B)) = _ at hSolve
    simpa only [← ContinuousLinearMap.comp_assoc,hM.inverse_comp_self,ContinuousLinearMap.id_comp] using hSolve
  have hNormalTerm : ‖(M-c • ContinuousLinearMap.id ℝ F-r • M1).comp D‖ ≤ QM*‖D‖*r^2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right hNormal (norm_nonneg _)).trans_eq (by ring))
  have hSum : ‖S‖ ≤ QT*(∑ j : Fin 3,‖G j‖)*r^2 := by
    calc
      _ ≤ ∑ j : Fin 3,‖(T j).comp (G j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3,(QT*r^2)*‖G j‖ := Finset.sum_le_sum fun j _ =>
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hT j) (norm_nonneg _))
      _ = _ := by rw [← Finset.mul_sum];ring
  have hCross : ‖r • (M-c • ContinuousLinearMap.id ℝ F).comp B‖ ≤ DM*CB*r^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hDiff hFirst (norm_nonneg _) (mul_nonneg hDM hr))) hr).trans_eq (by ring)
  have hInside : ‖(N-c • D-r • N1)-(M-c • ContinuousLinearMap.id ℝ F-r • M1).comp D-S-
      r • (M-c • ContinuousLinearMap.id ℝ F).comp B‖ ≤
      (QN+QM*‖D‖+QT*∑ j : Fin 3,‖G j‖+DM*CB)*r^2 := by
    exact ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)).trans
        ((add_le_add (add_le_add (add_le_add hN hNormalTerm) hSum) hCross).trans_eq (by ring))
  rw [hEq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hInv hInside (norm_nonneg _) hCI).trans_eq (by ring))

end ShrinkingSpheres
