import Proof.Geometry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ShrinkingSpheres

/-- Contraction of the rotation action by a skew connection matrix is
    its usual vector representation, including the exact factor one half. -/
lemma skew_rotation_coefficient_contraction {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : I → I → ℝ) (hΓ : ∀ i j,Γ i j= -Γ j i) (c : I → ℝ) (T : I → E) :
    (∑ i : I,∑ j : I,((1/2:ℝ)*Γ i j) • (c j • T i-c i • T j))=
      ∑ i : I,(∑ j : I,Γ i j*c j) • T i := by
  have hSwap : (∑ i : I,∑ j : I,((1/2:ℝ)*Γ i j*c i) • T j)=
      -(∑ i : I,∑ j : I,((1/2:ℝ)*Γ i j*c j) • T i) := by
    calc
      _ = ∑ i : I,∑ j : I,((1/2:ℝ)*Γ j i*c j) • T i := Finset.sum_comm
      _ = ∑ i : I,∑ j : I,-(((1/2:ℝ)*Γ i j*c j) • T i) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hΓ j i,← neg_smul]
        congr 1
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  simp only [smul_sub,smul_smul,Finset.sum_sub_distrib]
  rw [hSwap,sub_neg_eq_add,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← add_smul]
  congr 1
  ring
end ShrinkingSpheres
