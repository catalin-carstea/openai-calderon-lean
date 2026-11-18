import Proof.ParallelEnergySectors

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy

lemma balanced_symmetric_scalar_graph {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T B : E →L[ℝ] E) (J Bh Ah : H →L[ℝ] E) (w : ℝ)
    (hB : T.comp Bh=B.comp J) (hA : T.comp Ah=B.adjoint.comp J) :
    T.comp (w • (Bh+Ah))=(w • (B+B.adjoint)).comp J := by
  rw [ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_add,hB,hA,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.add_comp]

lemma symmetric_scalar_adjoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : E →L[ℝ] E) (w : ℝ) :
    (w • (B+B.adjoint)).adjoint=w • (B+B.adjoint) := by
  rw [map_smul,map_add,ContinuousLinearMap.adjoint_adjoint,add_comm]

/-- Pure pairing algebra, with each already constructed row retained.
This uses no composition or regularity inference for angular operators. -/
lemma scalar_first_symmetric_split_algebra {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : ℝ) (S F U : E) (B : I → E →L[ℝ] E) (V D : I → E)
    (q : I → ℝ) (Z : I → E)
    (hZ : ∀ b,Z b=mu • ((B b).adjoint (V b)+D b)+q b • (B b).adjoint U) :
    2*(mu*(∑ b : I,⟪S,B b (V b)⟫_ℝ)+∑ b : I,⟪S+F,Z b⟫_ℝ)=
      2*(mu*(∑ b : I,⟪S,(B b+(B b).adjoint) (V b)⟫_ℝ)+
        (∑ b : I,⟪S,mu • D b+q b • (B b).adjoint U⟫_ℝ)+
        ∑ b : I,⟪F,Z b⟫_ℝ) := by
  simp only [hZ,_root_.add_apply,inner_add_left,inner_add_right,real_inner_smul_right,Fin.sum_univ_three]
  ring

end ShrinkingSpheres.ParallelEnergy
