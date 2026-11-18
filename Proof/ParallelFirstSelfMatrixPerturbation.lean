import Proof.FirstCommutatorFormBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The crossed-minus-divergence contraction on a three by three array. -/
def firstSelfMatrixExchange (V : I → I → F) : ℝ :=
  ∑ b : I,∑ c : I,(⟪V b c,V c b⟫_ℝ-⟪V b b,V c c⟫_ℝ)

lemma firstSelfMatrixExchange_sub_identity (G T : I → I → F) :
    firstSelfMatrixExchange (fun b i => G b i-T b i)-firstSelfMatrixExchange G=
      ∑ b : I,∑ c : I,(-⟪T b c,G c b⟫_ℝ-⟪G b c,T c b⟫_ℝ+⟪T b c,T c b⟫_ℝ+
        ⟪T b b,G c c⟫_ℝ+⟪G b b,T c c⟫_ℝ-⟪T b b,T c c⟫_ℝ) := by
  unfold firstSelfMatrixExchange
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp only [inner_sub_left,inner_sub_right]
  ring

private lemma abs_three_sum_le (x y z B : ℝ) (hx : |x| ≤ B) (hy : |y| ≤ B) (hz : |z| ≤ B) :
    |x+y+z| ≤ 3*B := by
  have h1 := abs_add_le (x+y) z
  have h2 := abs_add_le x y
  linarith only [h1,h2,hx,hy,hz]

/-- Pointwise perturbation of the whole exchange. In the physical caller,
these pair bounds come from positive-half jets paired with weak sources. -/
lemma firstSelfMatrixExchange_sub_bound (G T : I → I → F) (B : ℝ)
    (hTG : ∀ b i c j,|⟪T b i,G c j⟫_ℝ| ≤ B)
    (hTT : ∀ b i c j,|⟪T b i,T c j⟫_ℝ| ≤ B) :
    |firstSelfMatrixExchange (fun b i => G b i-T b i)-firstSelfMatrixExchange G| ≤ 54*B := by
  rw [firstSelfMatrixExchange_sub_identity]
  have hGT (b i c j : I) : |⟪G b i,T c j⟫_ℝ| ≤ B := by rw [real_inner_comm];exact hTG c j b i
  have hTerm (b c : I) : |-⟪T b c,G c b⟫_ℝ-⟪G b c,T c b⟫_ℝ+⟪T b c,T c b⟫_ℝ+
      ⟪T b b,G c c⟫_ℝ+⟪G b b,T c c⟫_ℝ-⟪T b b,T c c⟫_ℝ| ≤ 6*B := by
    have h1 := abs_three_sum_le (-⟪T b c,G c b⟫_ℝ) (-⟪G b c,T c b⟫_ℝ) ⟪T b c,T c b⟫_ℝ B
      (by simpa only [abs_neg] using hTG b c c b) (by simpa only [abs_neg] using hGT b c c b) (hTT b c c b)
    have h2 := abs_three_sum_le ⟪T b b,G c c⟫_ℝ ⟪G b b,T c c⟫_ℝ (-⟪T b b,T c c⟫_ℝ) B
      (hTG b b c c) (hGT b b c c) (by simpa only [abs_neg] using hTT b b c c)
    have hAbs := abs_add_le (-⟪T b c,G c b⟫_ℝ-⟪G b c,T c b⟫_ℝ+⟪T b c,T c b⟫_ℝ)
      (⟪T b b,G c c⟫_ℝ+⟪G b b,T c c⟫_ℝ-⟪T b b,T c c⟫_ℝ)
    have hEq : (-⟪T b c,G c b⟫_ℝ-⟪G b c,T c b⟫_ℝ+⟪T b c,T c b⟫_ℝ)+
        (⟪T b b,G c c⟫_ℝ+⟪G b b,T c c⟫_ℝ-⟪T b b,T c c⟫_ℝ)=
        -⟪T b c,G c b⟫_ℝ-⟪G b c,T c b⟫_ℝ+⟪T b c,T c b⟫_ℝ+
          ⟪T b b,G c c⟫_ℝ+⟪G b b,T c c⟫_ℝ-⟪T b b,T c c⟫_ℝ := by ring
    rw [hEq] at hAbs
    simp only [sub_eq_add_neg] at hAbs ⊢
    linarith only [hAbs,h1,h2]
  calc
    _ ≤ ∑ b : I,∑ c : I,|-⟪T b c,G c b⟫_ℝ-⟪G b c,T c b⟫_ℝ+⟪T b c,T c b⟫_ℝ+
        ⟪T b b,G c c⟫_ℝ+⟪G b b,T c c⟫_ℝ-⟪T b b,T c c⟫_ℝ| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _b : I,∑ _c : I,6*B := Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => hTerm b c))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end ShrinkingSpheres.ParallelEnergy
