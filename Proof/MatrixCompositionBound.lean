import Proof.BoundedCompositionCross
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Shared matrix-contracted composition estimate for the actual E/E and F/F callers. -/
lemma norm_matrix_composition_sum_le (A : Fin 3 → V →L[ℝ] W) (B : Fin 3 → U →L[ℝ] V)
    (Q : Fin 3 → Fin 3 → ℝ) {b cA cB : ℝ} (hb : 0 ≤ b) (hA : 0 ≤ cA)
    (hQ : ∀ i j,|Q i j| ≤ b) (hAn : ∀ i,‖A i‖ ≤ cA) (hBn : ∀ j,‖B j‖ ≤ cB) :
    ‖∑ i : Fin 3,∑ j : Fin 3,Q i j • (A i).comp (B j)‖ ≤ 9*b*cA*cB := by
  have hEach (i j : Fin 3) : ‖Q i j • (A i).comp (B j)‖ ≤ b*cA*cB := by
    rw [norm_smul,Real.norm_eq_abs]
    have hComp := (ContinuousLinearMap.opNorm_comp_le (A i) (B j)).trans
      (mul_le_mul (hAn i) (hBn j) (norm_nonneg _) hA)
    exact (mul_le_mul (hQ i j) hComp (norm_nonneg _) hb).trans_eq (by ring)
  calc
    _ ≤ ∑ i : Fin 3,∑ j : Fin 3,‖Q i j • (A i).comp (B j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin 3,∑ _j : Fin 3,b*cA*cB :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEach i j))
    _ = _ := by simp only [Fin.sum_univ_three];ring
end ShrinkingSpheres
