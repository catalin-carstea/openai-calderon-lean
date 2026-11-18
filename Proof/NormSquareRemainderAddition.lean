import Proof.CanonicalPrincipalLowerBound
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres

lemma norm_sq_add_le_of_sq_bounds {H : Type*} [SeminormedAddCommGroup H]
    (u v : H) {A B I : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (hu : ‖u‖^2 ≤ A^2*I) (hv : ‖v‖^2 ≤ B^2*I) :
    ‖u+v‖^2 ≤ (A+B)^2*I := by
  have hs := Real.sq_sqrt hI
  have hAS : 0 ≤ A*Real.sqrt I := mul_nonneg hA (Real.sqrt_nonneg _)
  have hBS : 0 ≤ B*Real.sqrt I := mul_nonneg hB (Real.sqrt_nonneg _)
  have hU : ‖u‖ ≤ A*Real.sqrt I :=
    (sq_le_sq₀ (norm_nonneg _) hAS).mp (by nlinarith only [hu,hs])
  have hV : ‖v‖ ≤ B*Real.sqrt I :=
    (sq_le_sq₀ (norm_nonneg _) hBS).mp (by nlinarith only [hv,hs])
  have hSum : ‖u+v‖ ≤ (A+B)*Real.sqrt I :=
    (norm_add_le _ _).trans ((add_le_add hU hV).trans_eq (by ring))
  have hSq := (sq_le_sq₀ (norm_nonneg (u+v)) (mul_nonneg (add_nonneg hA hB) (Real.sqrt_nonneg I))).mpr hSum
  nlinarith only [hSq,hs]
end ShrinkingSpheres
