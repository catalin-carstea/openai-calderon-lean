import Proof.ParallelScalarModelDefectProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy

lemma scalar_model_adjoint_sum_norm_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G : I → I → ℝ) (ell : I → ℝ) (R : I → E →L[ℝ] E) (V : I → E) (D : E)
    (K Q β u : ℝ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hβ : 0 ≤ β) (hu : 0 ≤ u)
    (hG : ∀ k c,|G k c| ≤ K) (hEll : ∀ k,|ell k| ≤ K*β)
    (hR : ∀ c,‖R c‖ ≤ Q) (hD : ‖D‖ ≤ 3*u) :
    ‖∑ k : I,∑ c : I,G k c • (-(R c).adjoint (V k)+ell k • (R c).adjoint D)‖ ≤
      (3*K*Q)*(∑ k : I,‖V k‖)+(27*K^2*Q)*β*u := by
  have hTerm (k c : I) : ‖G k c • (-(R c).adjoint (V k)+ell k • (R c).adjoint D)‖ ≤
      K*(Q*‖V k‖+(K*β)*(Q*(3*u))) := by
    have hA : ‖(R c).adjoint‖ ≤ Q := by rw [ContinuousLinearMap.adjoint.norm_map];exact hR c
    rw [norm_smul,Real.norm_eq_abs]
    apply mul_le_mul (hG k c) _ (norm_nonneg _) hK
    apply (norm_add_le _ _).trans
    rw [norm_neg,norm_smul,Real.norm_eq_abs]
    exact add_le_add (((R c).adjoint.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
      (mul_le_mul (hEll k) (((R c).adjoint.le_opNorm _).trans
        (mul_le_mul hA hD (norm_nonneg _) hQ)) (norm_nonneg _) (mul_nonneg hK hβ))
  calc
    _ ≤ ∑ k : I,∑ c : I,‖G k c • (-(R c).adjoint (V k)+ell k • (R c).adjoint D)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_sum_le _ _))
    _ ≤ ∑ k : I,∑ c : I,K*(Q*‖V k‖+(K*β)*(Q*(3*u))) :=
      Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun c _ => hTerm k c))
    _ = _ := by simp only [Fin.sum_univ_three];ring

lemma scalar_model_defect_sum_norm_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : F →L[ℝ] E) (hJ : ‖J‖ ≤ 1) (u : F) (V : I → E) (b : I → ℝ) (c B Z ε β : ℝ)
    (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hb : ∀ i,|b i| ≤ B*ε/β) (hc : |c| ≤ Z*ε) :
    ‖c • J u+∑ i : I,b i • V i‖ ≤ (B*ε/β)*(∑ i : I,‖V i‖)+(Z*ε)*‖u‖ := by
  have hJU : ‖J u‖ ≤ ‖u‖ := (J.le_opNorm u).trans
    ((mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans_eq (one_mul _))
  have hZero : ‖c • J u‖ ≤ (Z*ε)*‖u‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hc hJU (norm_nonneg _) (mul_nonneg hZ hε)
  have hFirst : ‖∑ i : I,b i • V i‖ ≤ (B*ε/β)*(∑ i : I,‖V i‖) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)
  exact (norm_add_le _ _).trans ((add_le_add hZero hFirst).trans_eq (add_comm _ _))

end ShrinkingSpheres.ParallelEnergy
