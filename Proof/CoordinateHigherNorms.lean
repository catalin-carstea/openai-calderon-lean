import Proof.ConnectionOperatorBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ShrinkingSpheres

/-- A coordinate bound controls the full operator norm of a bilinear map in
    the fixed three-dimensional Euclidean coordinates. -/
lemma norm_bilinear_le_of_axis_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : X →L[ℝ] X →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ i j,‖L (axis i) (axis j)‖ ≤ C) : ‖L‖ ≤ 9*C := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  have hExpand : L u v = ∑ i,∑ j,(u i*v j) • L (axis i) (axis j) := by
    conv_lhs => rw [← axis_expansion u,← axis_expansion v]
    simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hTerm (i j : I) : ‖(u i*v j) • L (axis i) (axis j)‖ ≤ ‖u‖*‖v‖*C := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    have hui : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    have hvj : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    gcongr
    exact hL i j
  rw [hExpand]
  calc
    _ ≤ ∑ i,‖∑ j,(u i*v j) • L (axis i) (axis j)‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖(u i*v j) • L (axis i) (axis j)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : I,∑ _j : I,‖u‖*‖v‖*C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma norm_fin3_triple_sum_le {E : Type*} [NormedAddCommGroup E]
    (f : I → I → I → E) (C : ℝ) (h : ∀ i j k,‖f i j k‖ ≤ C) :
    ‖∑ i,∑ j,∑ k,f i j k‖ ≤ 27*C := by
  calc
    _ ≤ ∑ i,‖∑ j,∑ k,f i j k‖ := norm_sum_le Finset.univ _
    _ ≤ ∑ i,∑ j,‖∑ k,f i j k‖ := Finset.sum_le_sum (fun i _ => norm_sum_le Finset.univ _)
    _ ≤ ∑ i,∑ j,∑ k,‖f i j k‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => norm_sum_le Finset.univ _))
    _ ≤ ∑ _i : I,∑ _j : I,∑ _k : I,C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => h i j k)))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end ShrinkingSpheres
