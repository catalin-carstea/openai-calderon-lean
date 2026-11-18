import Proof.ParallelScalarJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Uniform scalar composition bounds for the same local parallel input.
    Only one center derivative and one angular derivative are needed. -/
theorem parallelScalar_directional_bounds (F : X × X → ℝ) (g : MetricField)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (z b : X)
    (W : Set (X × X)) (hW : IsOpen W) (hp : (y,r • L z) ∈ W) (hF : ContDiffOn ℝ ∞ F W)
    (Q C N : ℝ) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hN : 0 ≤ N) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : ‖r • L z‖ ≤ 1) (hL : ‖L‖ ≤ N) (hGamma : ‖connectionBilinear g y‖ ≤ C)
    (hFirst : ‖fderiv ℝ F (y,r • L z)‖ ≤ Q)
    (hSecond : ‖fderiv ℝ (fderiv ℝ F) (y,r • L z)‖ ≤ Q) :
    |fderiv ℝ (F ∘ parallelFrameInput g y a r L) (0,z) (1,0)| ≤ Q*(1+C)*‖a‖ ∧
    |fderiv ℝ (F ∘ parallelFrameInput g y a r L) (0,z) (0,b)| ≤ Q*N*‖b‖ ∧
    |fderiv ℝ (fderiv ℝ (F ∘ parallelFrameInput g y a r L)) (0,z) (0,b) (1,0)| ≤
      Q*(1+2*C)*N*‖a‖*‖b‖ := by
  have hF0 := hF.contDiffAt (hW.mem_nhds hp)
  have hGammaApply (v : X) : ‖connection g y a v‖ ≤ C*‖a‖*‖v‖ := by
    rw [← connectionBilinear_apply]
    exact (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have hAngle : ‖r • L b‖ ≤ N*‖b‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left ((L.le_opNorm b).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg b))) hr).trans
      (mul_le_of_le_one_left (mul_nonneg hN (norm_nonneg b)) hr1)
  have hDirection : ‖((a,-connection g y a (r • L z)):X × X)‖ ≤ (1+C)*‖a‖ := by
    rw [Prod.norm_mk,norm_neg]
    refine max_le ?_ ?_
    · nlinarith only [mul_nonneg hC (norm_nonneg a)]
    · exact (hGammaApply _).trans ((mul_le_mul_of_nonneg_left hv (mul_nonneg hC (norm_nonneg a))).trans
        (by nlinarith only [norm_nonneg a]))
  have hVertical : ‖((0,r • L b):X × X)‖ ≤ N*‖b‖ := by
    simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg _)] using hAngle
  have hMixedInput : ‖((0,-connection g y a (r • L b)):X × X)‖ ≤ C*‖a‖*(N*‖b‖) := by
    simp only [Prod.norm_mk,norm_zero,norm_neg,max_eq_right (norm_nonneg _)]
    exact (hGammaApply _).trans (mul_le_mul_of_nonneg_left hAngle (mul_nonneg hC (norm_nonneg a)))
  refine ⟨?_,?_,?_⟩
  · rw [fderiv_comp_parallelFrameInput_center F g y a r L z hF0,← Real.norm_eq_abs]
    exact ((fderiv ℝ F _).le_opNorm _).trans ((show ‖fderiv ℝ F (y,r • L z)‖*
      ‖((a,-connection g y a (r • L z)):X × X)‖ ≤ Q*((1+C)*‖a‖) by gcongr).trans_eq (by ring))
  · rw [fderiv_comp_parallelFrameInput_vertical F g y a r L z b hF0,← Real.norm_eq_abs]
    exact ((fderiv ℝ F _).le_opNorm _).trans ((show ‖fderiv ℝ F (y,r • L z)‖*‖((0,r • L b):X × X)‖ ≤ Q*(N*‖b‖) by gcongr).trans_eq (by ring))
  · rw [fderiv_comp_parallelFrameInput_mixed F g y a r L z b W hW hp hF,← Real.norm_eq_abs]
    have hTwo : ‖fderiv ℝ (fderiv ℝ F) (y,r • L z) (0,r • L b) (a,-connection g y a (r • L z))‖ ≤
        Q*(N*‖b‖)*((1+C)*‖a‖) :=
      (ContinuousLinearMap.le_opNorm₂ _ _ _).trans (by gcongr)
    have hOne : ‖fderiv ℝ F (y,r • L z) (0,-connection g y a (r • L b))‖ ≤ Q*(C*‖a‖*(N*‖b‖)) :=
      ((fderiv ℝ F _).le_opNorm _).trans (by gcongr)
    exact ((norm_add_le _ _).trans (add_le_add hTwo hOne)).trans_eq (by ring)

end ShrinkingSpheres
