import Proof.ParallelScalarFirstPairAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy

/-- Finite algebra for the complete corrected model/scalar pairing.
The scalar defect, both angular degree terms, and the symmetric leading
raising coefficient remain explicit. -/
lemma scalar_model_pair_split_algebra {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : ℝ) (A G : I → I → ℝ) (ell : I → ℝ) (R : I → E →L[ℝ] E)
    (H : I → I → E) (V : I → E) (D0 D1 F : E) :
    μ*(⟪(∑ a : I,∑ b : I,A a b • H a b),
        (∑ k : I,∑ c : I,G k c • (R c (V k)+ell k • R c D0))⟫_ℝ-
      ⟪(∑ a : I,∑ b : I,A a b • H a b)+F,
        (∑ k : I,∑ c : I,G k c • (-(R c).adjoint (V k)+ell k • (R c).adjoint D1))⟫_ℝ)=
    (∑ a : I,∑ b : I,∑ k : I,∑ c : I,μ*A a b*G k c*⟪H a b,(R c+(R c).adjoint) (V k)⟫_ℝ)+
    (∑ k : I,∑ c : I,∑ a : I,∑ b : I,μ*A a b*G k c*ell k*(
      ⟪D0,(R c).adjoint (H a b)⟫_ℝ-⟪D1,R c (H a b)⟫_ℝ))-
    μ*⟪F,(∑ k : I,∑ c : I,G k c • (-(R c).adjoint (V k)+ell k • (R c).adjoint D1))⟫_ℝ := by
  have h0 (a b c : I) : ⟪H a b,R c D0⟫_ℝ=⟪D0,(R c).adjoint (H a b)⟫_ℝ := by
    rw [(R c).adjoint_inner_right,real_inner_comm]
  have h1 (a b c : I) : ⟪H a b,(R c).adjoint D1⟫_ℝ=⟪D1,R c (H a b)⟫_ℝ := by
    rw [(R c).adjoint_inner_right,real_inner_comm]
  simp only [inner_sum,sum_inner,real_inner_smul_left,real_inner_smul_right,inner_add_left,inner_add_right,
    inner_neg_right,_root_.add_apply,Finset.mul_sum,Finset.sum_mul]
  simp_rw [h0,h1]
  simp only [Fin.sum_univ_three]
  ring

end ShrinkingSpheres.ParallelEnergy
