import Proof.ConnectionOperatorBounds

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 10
open Set
namespace ShrinkingSpheres

/-- Adaptation of the selected archive CurvatureRotation norm estimate to the actual
    coordinate connection used by the frozen contract. -/
lemma norm_curvatureLinear_le (Γ : X → X →L[ℝ] X →L[ℝ] X) (y a b : X) :
    ‖curvatureLinear Γ y a b‖ ≤ 2*(‖fderiv ℝ Γ y‖+‖Γ y‖^2)*‖a‖*‖b‖ := by
  have hd1 := ((fderiv ℝ Γ y a).le_opNorm b).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ Γ y).le_opNorm a) (norm_nonneg b))
  have hd2 := ((fderiv ℝ Γ y b).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ Γ y).le_opNorm b) (norm_nonneg a))
  have hg1 := ((Γ y a).opNorm_comp_le (Γ y b)).trans
    (mul_le_mul ((Γ y).le_opNorm a) ((Γ y).le_opNorm b) (norm_nonneg _) (by positivity))
  have hg2 := ((Γ y b).opNorm_comp_le (Γ y a)).trans
    (mul_le_mul ((Γ y).le_opNorm b) ((Γ y).le_opNorm a) (norm_nonneg _) (by positivity))
  have ht1 := norm_sub_le ((fderiv ℝ Γ y a) b) ((fderiv ℝ Γ y b) a)
  have ht2 := norm_add_le ((fderiv ℝ Γ y a) b - (fderiv ℝ Γ y b) a) ((Γ y a).comp (Γ y b))
  have ht3 := norm_sub_le
    ((fderiv ℝ Γ y a) b - (fderiv ℝ Γ y b) a + (Γ y a).comp (Γ y b)) ((Γ y b).comp (Γ y a))
  unfold curvatureLinear
  nlinarith

lemma metricCurvature_norm_of_operator_bounds (g : MetricField) (y : X) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hΓ : ‖connectionBilinear g y‖ ≤ C)
    (hΓ' : ‖fderiv ℝ (connectionBilinear g) y‖ ≤ D) (a b w : X) :
    ‖metricCurvature g y a b w‖ ≤ 2*(D+C^2)*‖a‖*‖b‖*‖w‖ := by
  have hsq : ‖connectionBilinear g y‖^2 ≤ C^2 := (sq_le_sq₀ (norm_nonneg _) hC).2 hΓ
  have hc := norm_curvatureLinear_le (connectionBilinear g) y a b
  have hc' : ‖curvatureLinear (connectionBilinear g) y a b‖ ≤ 2*(D+C^2)*‖a‖*‖b‖ := by
    apply hc.trans
    gcongr
  change ‖coordinateCurvature (connectionBilinear g) y a b w‖ ≤ _
  rw [← curvatureLinear_apply]
  exact ((curvatureLinear (connectionBilinear g) y a b).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right hc' (norm_nonneg w))

lemma metricPair_abs_le_of_entry_bound (g : MetricField) (y : X) (M₀ : ℝ) (hM : 0 ≤ M₀)
    (hg : ∀ i j, |g y i j| ≤ M₀) (u v : X) :
    |metricPair g y u v| ≤ 9*M₀*‖u‖*‖v‖ := by
  have hterm (i j : I) : |g y i j*u i*v j| ≤ M₀*‖u‖*‖v‖ := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hg i j) (PiLp.norm_apply_le u i) (abs_nonneg _) hM)
      (PiLp.norm_apply_le v j) (abs_nonneg _) (by positivity)
  unfold metricPair
  calc
    _ ≤ ∑ i, ∑ j, |g y i j*u i*v j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : I, ∑ _j : I, M₀*‖u‖*‖v‖ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Curvature coefficients in any actual orthonormal frame, with no derivative budget on
    that frame. Its size is controlled directly by ellipticity. -/
theorem Elliptic.frameCurvatureCoefficient_bound {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (hframe : ∀ y ∈ Ω, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {y : X} (hy : y ∈ Ω) (M₀ C D : ℝ) (hM : 0 ≤ M₀) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ i j, |g y i j| ≤ M₀) (hΓ : ‖connectionBilinear g y‖ ≤ C)
    (hΓ' : ‖fderiv ℝ (connectionBilinear g) y‖ ≤ D) (i j a b : I) :
    |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ 18*M₀*(D+C^2)*K^2 := by
  have he (i : I) : ‖e y i‖ ≤ Real.sqrt K := Real.le_sqrt_of_sq_le (h.frame_norm_sq_bound hK e hframe hy i)
  have hcurv := metricCurvature_norm_of_operator_bounds g y C D hC hD hΓ hΓ' (e y i) (e y j) (e y a)
  calc
    _ ≤ 9*M₀*‖metricCurvature g y (e y i) (e y j) (e y a)‖*‖e y b‖ :=
      metricPair_abs_le_of_entry_bound g y M₀ hM hg _ _
    _ ≤ 9*M₀*(2*(D+C^2)*‖e y i‖*‖e y j‖*‖e y a‖)*‖e y b‖ := by gcongr
    _ ≤ 9*M₀*(2*(D+C^2)*Real.sqrt K*Real.sqrt K*Real.sqrt K)*Real.sqrt K := by gcongr <;> exact he _
    _ = 18*M₀*(D+C^2)*(Real.sqrt K^2)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hK.le]

end ShrinkingSpheres
