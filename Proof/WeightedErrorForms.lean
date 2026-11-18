import Proof.FullEnergyLimit
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace ShrinkingSpheres

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma weighted_product_le (a b β : ℝ) (hβ : 0 < β) : a*b ≤ β⁻¹*a^2+β*b^2 := by
  have ht : β*(a*b) ≤ a^2+β^2*b^2 := by nlinarith [sq_nonneg (a-β*b)]
  have heq : β*(β⁻¹*a^2+β*b^2) = a^2+β^2*b^2 := by
    rw [mul_add,← mul_assoc,mul_inv_cancel₀ hβ.ne',one_mul]
    ring
  exact (mul_le_mul_iff_right₀ hβ).mp (heq.symm ▸ ht)

def errorEnergy (β : ℝ) (H : I → F) (V : F) : ℝ := β⁻¹*(∑ i,‖H i‖^2)+β*‖V‖^2

def weightedErrorForm (β : ℝ) (H : I → F) (V : F)
    (B : I → I → F →L[ℝ] F) (C : I → F →L[ℝ] F) (Z : F →L[ℝ] F) : ℝ :=
  (∑ i,∑ j,β⁻¹*⟪B i j (H i),H j⟫_ℝ)+(∑ i,⟪C i (H i),V⟫_ℝ)+β*⟪Z V,V⟫_ℝ

lemma errorEnergy_nonneg (β : ℝ) (hβ : 0 ≤ β) (H : I → F) (V : F) : 0 ≤ errorEnergy β H V :=
  add_nonneg (mul_nonneg (inv_nonneg.mpr hβ) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (mul_nonneg hβ (sq_nonneg _))

lemma abs_inner_apply_le (A : F →L[ℝ] F) (u v : F) {q : ℝ} (hA : ‖A‖ ≤ q) :
    |⟪A u,v⟫_ℝ| ≤ q*‖u‖*‖v‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    ((A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) (norm_nonneg _))

/-- A form in the three permitted post-integration-by-parts types is controlled by the
    inverse-beta derivative square and beta times the three-halves angular square. -/
theorem weightedErrorForm_bound (β : ℝ) (hβ : 0 < β) (H : I → F) (V : F)
    (B : I → I → F →L[ℝ] F) (C : I → F →L[ℝ] F) (Z : F →L[ℝ] F) {q : ℝ} (hq : 0 ≤ q)
    (hB : ∀ i j,‖B i j‖ ≤ q) (hC : ∀ i,‖C i‖ ≤ q) (hZ : ‖Z‖ ≤ q) :
    |weightedErrorForm β H V B C Z| ≤ 13*q*errorEnergy β H V := by
  let W := errorEnergy β H V
  have hW : 0 ≤ W := errorEnergy_nonneg β hβ.le H V
  have hSum (i : I) : ‖H i‖^2 ≤ ∑ j,‖H j‖^2 := Finset.single_le_sum (f:=fun j : I => ‖H j‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hgrad : β⁻¹*(∑ i,‖H i‖^2) ≤ W := by
    exact le_add_of_nonneg_right (mul_nonneg hβ.le (sq_nonneg _))
  have hmass : β*‖V‖^2 ≤ W := by
    exact le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hβ.le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hbnd (i j : I) : |β⁻¹*⟪B i j (H i),H j⟫_ℝ| ≤ q*W := by
    have hprod : ‖H i‖*‖H j‖ ≤ ∑ k,‖H k‖^2 := by nlinarith [hSum i,hSum j,sq_nonneg (‖H i‖-‖H j‖)]
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hβ.le)]
    calc
      _ ≤ β⁻¹*(q*(‖H i‖*‖H j‖)) := mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using abs_inner_apply_le (B i j) (H i) (H j) (hB i j)) (inv_nonneg.mpr hβ.le)
      _ ≤ β⁻¹*(q*(∑ k,‖H k‖^2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hq) (inv_nonneg.mpr hβ.le)
      _ ≤ q*W := by nlinarith [mul_le_mul_of_nonneg_left hgrad hq]
  have hcbnd (i : I) : |⟪C i (H i),V⟫_ℝ| ≤ q*W := by
    have hp := weighted_product_le ‖H i‖ ‖V‖ β hβ
    have hs := mul_le_mul_of_nonneg_left (hSum i) (inv_nonneg.mpr hβ.le)
    have hi : ‖H i‖*‖V‖ ≤ W := by dsimp only [W,errorEnergy]; linarith
    exact (abs_inner_apply_le (C i) (H i) V (hC i)).trans (by nlinarith [mul_le_mul_of_nonneg_left hi hq])
  have hzbnd : |β*⟪Z V,V⟫_ℝ| ≤ q*W := by
    rw [abs_mul,abs_of_pos hβ]
    have hz := mul_le_mul_of_nonneg_left (abs_inner_apply_le Z V V hZ) hβ.le
    nlinarith [mul_le_mul_of_nonneg_left hmass hq]
  have hsumB : |∑ i,∑ j,β⁻¹*⟪B i j (H i),H j⟫_ℝ| ≤ 9*(q*W) := by
    calc
      _ ≤ ∑ i,∑ j,|β⁻¹*⟪B i j (H i),H j⟫_ℝ| := (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ _i : I,∑ _j : I,q*W := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbnd i j))
      _ = _ := by simp [I] <;> ring
  have hsumC : |∑ i,⟪C i (H i),V⟫_ℝ| ≤ 3*(q*W) := by
    calc
      _ ≤ ∑ i,|⟪C i (H i),V⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : I,q*W := Finset.sum_le_sum (fun i _ => hcbnd i)
      _ = _ := by simp [I] <;> ring
  unfold weightedErrorForm
  have habs := (abs_add_le ((∑ i,∑ j,β⁻¹*⟪B i j (H i),H j⟫_ℝ)+(∑ i,⟪C i (H i),V⟫_ℝ)) (β*⟪Z V,V⟫_ℝ)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  nlinarith only [habs,hsumB,hsumC,hzbnd]

end ShrinkingSpheres
