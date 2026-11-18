import Proof.WeightedErrorForms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ShrinkingSpheres

/-- The four actual reduced scalar/model-defect forms have precisely the
inverse-beta derivative and beta mass weights of the frozen energy. -/
theorem scalar_model_defect_four_form_bound
    (q dq x₁ x₂ x₃ x₄ mu A A1 CZ CZ1 CA ε β Ha Hb V : ℝ)
    (hmu : 0 ≤ mu) (hA : 0 ≤ A) (hA1 : 0 ≤ A1) (hCZ : 0 ≤ CZ) (hCZ1 : 0 ≤ CZ1)
    (hCA : 0 ≤ CA) (hε : 0 ≤ ε) (hβ : 0 < β) (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb) (hV : 0 ≤ V)
    (hq : |q| ≤ mu*A*ε/β^2) (hdq : |dq| ≤ mu*A1*ε/β)
    (hx1 : |x₁| ≤ CZ*β*Ha*Hb) (hx2 : |x₂| ≤ CZ1*β^2*Ha*V)
    (hx3 : |x₃| ≤ CA*β*V*Hb) (hx4 : |x₄| ≤ CZ1*β^2*V^2) :
    |-q*(x₁+x₂)-dq*(x₃+x₄)| ≤
      (A*CZ+A*CZ1+A1*CA+A1*CZ1)*mu*ε*
        ((β⁻¹*Ha^2+β*V^2)+(β⁻¹*Hb^2+β*V^2)) := by
  let W := (β⁻¹*Ha^2+β*V^2)+(β⁻¹*Hb^2+β*V^2)
  have hW0 : 0 ≤ W := by dsimp only [W];positivity
  have hEb0 : 0 ≤ β⁻¹*Hb^2+β*V^2 := by positivity
  have hCross : β⁻¹*Ha*Hb ≤ W := by
    have hh := mul_nonneg (inv_nonneg.mpr hβ.le) (sq_nonneg (Ha-Hb))
    have hm : 0 ≤ β*V^2 := by positivity
    have hp : 0 ≤ β⁻¹*Ha*Hb := by positivity
    dsimp only [W]
    nlinarith only [hh,hm,hp]
  have hHV : Ha*V ≤ W := (weighted_product_le Ha V β hβ).trans (le_add_of_nonneg_right hEb0)
  have hVH : V*Hb ≤ W := by
    have hh := weighted_product_le Hb V β hβ
    have hRest : 0 ≤ β⁻¹*Ha^2+β*V^2 := by positivity
    dsimp only [W]
    nlinarith only [hh,hRest]
  have hM : β*V^2 ≤ W := (le_add_of_nonneg_left
    (by positivity : 0 ≤ β⁻¹*Ha^2)).trans (le_add_of_nonneg_right hEb0)
  have h1 : |q*x₁| ≤ (mu*ε*(A*CZ))*W := by
    calc
      _ = |q| *|x₁| := abs_mul _ _
      _ ≤ (mu*A*ε/β^2)*(CZ*β*Ha*Hb) := mul_le_mul hq hx1 (abs_nonneg _) (by positivity)
      _ = (mu*ε*(A*CZ))*(β⁻¹*Ha*Hb) := by field_simp [hβ.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCross (by positivity)
  have h2 : |q*x₂| ≤ (mu*ε*(A*CZ1))*W := by
    calc
      _ = |q| *|x₂| := abs_mul _ _
      _ ≤ (mu*A*ε/β^2)*(CZ1*β^2*Ha*V) := mul_le_mul hq hx2 (abs_nonneg _) (by positivity)
      _ = (mu*ε*(A*CZ1))*(Ha*V) := by field_simp [hβ.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hHV (by positivity)
  have h3 : |dq*x₃| ≤ (mu*ε*(A1*CA))*W := by
    calc
      _ = |dq| *|x₃| := abs_mul _ _
      _ ≤ (mu*A1*ε/β)*(CA*β*V*Hb) := mul_le_mul hdq hx3 (abs_nonneg _) (by positivity)
      _ = (mu*ε*(A1*CA))*(V*Hb) := by field_simp [hβ.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hVH (by positivity)
  have h4 : |dq*x₄| ≤ (mu*ε*(A1*CZ1))*W := by
    calc
      _ = |dq| *|x₄| := abs_mul _ _
      _ ≤ (mu*A1*ε/β)*(CZ1*β^2*V^2) := mul_le_mul hdq hx4 (abs_nonneg _) (by positivity)
      _ = (mu*ε*(A1*CZ1))*(β*V^2) := by field_simp [hβ.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)
  calc
    _ = |-(q*x₁+q*x₂+dq*x₃+dq*x₄)| := by congr 1 <;> ring
    _ = |q*x₁+q*x₂+dq*x₃+dq*x₄| := abs_neg _
    _ ≤ |q*x₁+q*x₂+dq*x₃|+|dq*x₄| := abs_add_le _ _
    _ ≤ (|q*x₁+q*x₂|+|dq*x₃|)+|dq*x₄| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((|q*x₁|+|q*x₂|)+|dq*x₃|)+|dq*x₄| := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ ((mu*ε*(A*CZ))*W+(mu*ε*(A*CZ1))*W)+(mu*ε*(A1*CA))*W+(mu*ε*(A1*CZ1))*W :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by dsimp only [W];ring

end ShrinkingSpheres
